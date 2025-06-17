# Remember to execute this file in e.g. the following way (from the root folder): python -m finer_grained_tests.test_check_by_range_restriction 
from model import prover9_parser
from check_by_range_restriction import *

def test_satisfies_equalities():
    h=("X","X","Y","Z","Y")
    h2=("X","Y","Z","V","W")
    s=[(1,1,2,3,2),(2,2,1,3,1),(1,2,3,4,5),(1,1,1,1,2),(1,2,3,3,3)]
    g=[True, True, False, False, False]
    for tup, ground in zip(s,g):
        assert satisfies_equalities(h,tup) == ground
        assert satisfies_equalities(h2,tup) == True
    print("All good for filter equalities")

def showcase_bond_evaluation():
    p9model = P9ModelReader()
    for model_raw, formula_raw in [("A(a).B(b).E(a,b).E(b,c).R(c,e).U(e,b).","((exists Z exists Y (E(X,Z) & R(Z,Y))) | (exists Y2 U(Y2,X)))."),
        ("A(a,b).B(a,c).V(a,b,z).","(exists Y A(X,Y) & exists Z B(X,Z))."),
        ("A(a,a).B(a,c).V(a,b,z).","(A(X,X) & exists Z B(X,Z))."),
        ("A(a,b).B(a,c).V(a,b,z).","(A(X,X) & exists Z B(X,Z)).")]:
        model = p9model.read_model(prover9_parser.parse(model_raw))
        formula = RemoveLines().transform(prover9_parser.parse(formula_raw))
    
        evBound = evaluateQuantifierBound("X", model)
        treeExplainerGREEN(model)
        treeExplainerRED(formula)
        x = evBound.transform(formula)
        print(f"From the model in the GREEN tree and the formula in the RED tree, evaluates the formula against the model as if the formula were a quantifier bound. The resilt is {x}")

def test_range_and_bounded_minification():
    assert GetRange().adjust_transform_repeatedly(EXAMPLE_ASTS[0]) == Tree("existential_quantification", [Token('VARIABLE', 'Y'), Tree("predicate", [Token("PREDICATE_SYMBOL","att"), Token("VARIABLE","X"), Token("VARIABLE","Y")])]), GetRange().adjust_transform_repeatedly(EXAMPLE_ASTS[0])
    
    assert GetRange().adjust_transform_repeatedly(GetRange().adjust_transform_repeatedly(EXAMPLE_ASTS[0])) == Tree("existential_quantification", [Token('VARIABLE', 'X'), Tree("predicate", [Token("PREDICATE_SYMBOL","att"), Token("VARIABLE","X"), Token("VARIABLE","Y")])]), GetRange().adjust_transform_repeatedly(EXAMPLE_ASTS[0])
    
    # TODO: the following tests are outdated and should be removed or updated
    # calc = toBoundedMinifiedPCNF().adjust_transform_repeatedly(EXAMPLE_ASTS[0])
    # ground = Tree('disjunction', [Tree('universal_quantification_bounded', [Token('VARIABLE', 'Y'), Tree('predicate', [Token('PREDICATE_SYMBOL', 'lec'), Token('VARIABLE', 'Y')]), Tree('negation', [Tree('predicate', [Token('PREDICATE_SYMBOL', 'lec'), Token('VARIABLE', 'Y')])])]), Tree('existential_quantification_bounded', [Token('VARIABLE', 'X'), Tree('existential_quantification', [Token('VARIABLE', 'Y1'), Tree('predicate', [Token('PREDICATE_SYMBOL', 'att'), Token('VARIABLE', 'X'), Token('VARIABLE', 'Y1')])]), Tree('universal_quantification_bounded', [Token('VARIABLE', 'Y2'), Tree('predicate', [Token('PREDICATE_SYMBOL', 'lec'), Token('VARIABLE', 'Y2')]), Tree('disjunction', [Tree('negation', [Tree(Token('RULE', 'predicate'), [Token('PREDICATE_SYMBOL', 'lec'), Token('VARIABLE', 'Y2')])]), Tree(Token('RULE', 'predicate'), [Token('PREDICATE_SYMBOL', 'att'), Token('VARIABLE', 'X'), Token('VARIABLE', 'Y2')])])])])])
    # assert calc == ground, f"Expected green tree, actually got red one, which is {calc}{treeExplainerGREEN(ground)}{treeExplainerRED(calc)}" 
    
    # assert toBoundedMinifiedPCNF().adjust_transform_repeatedly(EXAMPLE_ASTS[1]) == Tree('existential_quantification_bounded', [Token('VARIABLE', 'X1'), Tree('dom', [Token('VARIABLE', 'X1')]), Tree('universal_quantification_bounded', [Token('VARIABLE', 'Y'), Tree('existential_quantification', ['X', Tree('predicate', [Token('PREDICATE_SYMBOL', 'P'), Token('VARIABLE', 'X'), Token('VARIABLE', 'Y')])]), Tree('disjunction', [Tree('negation', [Tree(Token('RULE', 'predicate'), [Token('PREDICATE_SYMBOL', 'P'), Token('VARIABLE', 'X1'), Token('VARIABLE', 'Y')])]), Tree(Token('RULE', 'predicate'), [Token('PREDICATE_SYMBOL', 'Q'), Token('VARIABLE', 'X1'), Token('VARIABLE', 'Y')])])])])
    
    # assert toBoundedMinifiedPCNF().adjust_transform_repeatedly(EXAMPLE_ASTS[2]) == Tree('disjunction', [Tree(Token('RULE', 'predicate'), [Token('PREDICATE_SYMBOL', 'U'), Token('VARIABLE', 'V')]), Tree('existential_quantification_bounded', [Token('VARIABLE', 'X1'), Tree('dom', [Token('VARIABLE', 'X1')]), Tree('universal_quantification_bounded', [Token('VARIABLE', 'Y'), Tree('existential_quantification', ['X', Tree('predicate', [Token('PREDICATE_SYMBOL', 'P'), Token('VARIABLE', 'X'), Token('VARIABLE', 'Y')])]), Tree('disjunction', [Tree('negation', [Tree(Token('RULE', 'predicate'), [Token('PREDICATE_SYMBOL', 'P'), Token('VARIABLE', 'X1'), Token('VARIABLE', 'Y')])]), Tree(Token('RULE', 'predicate'), [Token('PREDICATE_SYMBOL', 'Q'), Token('VARIABLE', 'X1'), Token('VARIABLE', 'Y')])])])])])
    
    # ground = Tree('universal_quantification_bounded', [Token('VARIABLE', 'Y'), Tree('predicate', [Token('PREDICATE_SYMBOL', 'lec'), Token('VARIABLE', 'Y')]), Tree('disjunction', [Tree('negation', [Tree(Token('RULE', 'predicate'), [Token('PREDICATE_SYMBOL', 'lec'), Token('VARIABLE', 'Y')])]), Tree('universal_quantification_bounded', [Token('VARIABLE', 'X'), Tree('dom', [Token('VARIABLE', 'X')]), Tree(Token('RULE', 'predicate'), [Token('PREDICATE_SYMBOL', 'att'), Token('VARIABLE', 'X'), Token('VARIABLE', 'Y')])])])])
    # calc = toBoundedMinifiedPCNF().adjust_transform_repeatedly(EXAMPLE_ASTS[3])
    # assert calc == ground, f"I got the red tree, but I should have got the green one (all starting from the black and white tree) {treeExplainerRED(calc)}{treeExplainerGREEN(ground)}{treeExplainer(EXAMPLE_ASTS[3])}---\n\nString>>>{ToString().visit(calc)}" 

    
    # assert toBoundedMinifiedPCNF().adjust_transform_repeatedly(EXAMPLE_ASTS[4]) == Tree('predicate', [Token('PREDICATE_SYMBOL', 'att'), Token('VARIABLE', 'X'), Token('VARIABLE', 'Y')])
    
    # assert toBoundedMinifiedPCNF().adjust_transform_repeatedly(EXAMPLE_ASTS[5]) == Tree('universal_quantification_bounded', [Token('VARIABLE', 'X'), Tree('conjunction', [Tree('predicate', [Token('PREDICATE_SYMBOL', 'B'), Token('VARIABLE', 'X')]), Tree('existential_quantification', ['Y', Tree('predicate', [Token('PREDICATE_SYMBOL', 'att'), Token('VARIABLE', 'X'), Token('VARIABLE', 'Y')])])]), Tree('disjunction', [Tree('negation', [Tree(Token('RULE', 'predicate'), [Token('PREDICATE_SYMBOL', 'B'), Token('VARIABLE', 'X')])]), Tree('negation', [Tree(Token('RULE', 'predicate'), [Token('PREDICATE_SYMBOL', 'att'), Token('VARIABLE', 'X'), Token('VARIABLE', 'Y')])])])])
    
    
    # base = EXAMPLE_ASTS[6]
    # ground = Tree('universal_quantification_bounded', [Token('VARIABLE', 'Y4'), Tree('conjunction', [Tree('existential_quantification', [Token('VARIABLE', 'Z'), Tree('existential_quantification', [Token('VARIABLE', 'TAU'), Tree('predicate', [Token('PREDICATE_SYMBOL', 'cP'), Token('VARIABLE', 'Y4'), Token('VARIABLE', 'Z'), Token('VARIABLE', 'TAU')])])]), Tree('existential_quantification', [Token('VARIABLE', 'T'), Tree('existential_quantification', [Token('VARIABLE', 'X'), Tree('predicate', [Token('PREDICATE_SYMBOL', 'cP'), Token('VARIABLE', 'X'), Token('VARIABLE', 'Y4'), Token('VARIABLE', 'T')])])])]), Tree('universal_quantification_bounded', [Token('VARIABLE', 'Z2'), Tree('existential_quantification', ['Y', Tree('existential_quantification', [Token('VARIABLE', 'TAU1'), Tree('predicate', [Token('PREDICATE_SYMBOL', 'cP'), Token('VARIABLE', 'Y'), Token('VARIABLE', 'Z2'), Token('VARIABLE', 'TAU1')])])]), Tree('universal_quantification_bounded', [Token('VARIABLE', 'T3'), Tree('conjunction', [Tree('existential_quantification', [Token('VARIABLE', 'TAU2'), Tree('predicate', [Token('PREDICATE_SYMBOL', 'tP'), Token('VARIABLE', 'T3'), Token('VARIABLE', 'TAU2')])]), Tree('existential_quantification', [Token('VARIABLE', 'Y1'), Tree('existential_quantification', [Token('VARIABLE', 'X1'), Tree('predicate', [Token('PREDICATE_SYMBOL', 'cP'), Token('VARIABLE', 'X1'), Token('VARIABLE', 'Y1'), Token('VARIABLE', 'T3')])])])]), Tree('disjunction', [Tree('universal_quantification_bounded', [Token('VARIABLE', 'TAU3'), Tree('conjunction', [Tree('existential_quantification', [Token('VARIABLE', 'Z1'), Tree('existential_quantification', [Token('VARIABLE', 'Y2'), Tree('predicate', [Token('PREDICATE_SYMBOL', 'cP'), Token('VARIABLE', 'Y2'), Token('VARIABLE', 'Z1'), Token('VARIABLE', 'TAU3')])])]), Tree('existential_quantification', [Token('VARIABLE', 'T1'), Tree('predicate', [Token('PREDICATE_SYMBOL', 'tP'), Token('VARIABLE', 'T1'), Token('VARIABLE', 'TAU3')])])]), Tree('disjunction', [Tree('negation', [Tree(Token('RULE', 'predicate'), [Token('PREDICATE_SYMBOL', 'cP'), Token('VARIABLE', 'Y4'), Token('VARIABLE', 'Z2'), Token('VARIABLE', 'TAU3')])]), Tree('negation', [Tree(Token('RULE', 'predicate'), [Token('PREDICATE_SYMBOL', 'tP'), Token('VARIABLE', 'T3'), Token('VARIABLE', 'TAU3')])])])]), Tree('universal_quantification_bounded', [Token('VARIABLE', 'X2'), Tree('existential_quantification', [Token('VARIABLE', 'Y3'), Tree('existential_quantification', [Token('VARIABLE', 'T2'), Tree('predicate', [Token('PREDICATE_SYMBOL', 'cP'), Token('VARIABLE', 'X2'), Token('VARIABLE', 'Y3'), Token('VARIABLE', 'T2')])])]), Tree('disjunction', [Tree('negation', [Tree(Token('RULE', 'predicate'), [Token('PREDICATE_SYMBOL', 'cP'), Token('VARIABLE', 'X2'), Token('VARIABLE', 'Y4'), Token('VARIABLE', 'T3')])]), Tree(Token('RULE', 'predicate'), [Token('PREDICATE_SYMBOL', 'cP'), Token('VARIABLE', 'X2'), Token('VARIABLE', 'Z2'), Token('VARIABLE', 'T3')])])])])])])])
    # calc = toBoundedMinifiedPCNF().adjust_transform_repeatedly(base)
    # assert calc == ground, f"From black/white should have got green, got red (=string) instead {treeExplainer(base), treeExplainerGREEN(ground), treeExplainerRED(calc), calc}"
    
    # base = EXAMPLE_ASTS[7]
    # ground = Tree('universal_quantification_bounded', [Token('VARIABLE', 'R3'), Tree('conjunction', [Tree('existential_quantification', [Token('VARIABLE', 'S'), Tree('predicate', [Token('PREDICATE_SYMBOL', 'temporalPartOf'), Token('VARIABLE', 'S'), Token('VARIABLE', 'R3')])]), Tree('existential_quantification', [Token('VARIABLE', 'Q'), Tree('existential_quantification', [Token('VARIABLE', 'P'), Tree('predicate', [Token('PREDICATE_SYMBOL', 'continuantPartOf'), Token('VARIABLE', 'P'), Token('VARIABLE', 'Q'), Token('VARIABLE', 'R3')])])])]), Tree('universal_quantification_bounded', [Token('VARIABLE', 'S1'), Tree('existential_quantification', ['R', Tree('predicate', [Token('PREDICATE_SYMBOL', 'temporalPartOf'), Token('VARIABLE', 'S1'), Token('VARIABLE', 'R')])]), Tree('disjunction', [Tree('negation', [Tree(Token('RULE', 'predicate'), [Token('PREDICATE_SYMBOL', 'temporalPartOf'), Token('VARIABLE', 'S1'), Token('VARIABLE', 'R3')])]), Tree('universal_quantification_bounded', [Token('VARIABLE', 'Q2'), Tree('existential_quantification', [Token('VARIABLE', 'R1'), Tree('existential_quantification', [Token('VARIABLE', 'P1'), Tree('predicate', [Token('PREDICATE_SYMBOL', 'continuantPartOf'), Token('VARIABLE', 'P1'), Token('VARIABLE', 'Q2'), Token('VARIABLE', 'R1')])])]), Tree('universal_quantification_bounded', [Token('VARIABLE', 'P2'), Tree('existential_quantification', [Token('VARIABLE', 'R2'), Tree('existential_quantification', [Token('VARIABLE', 'Q1'), Tree('predicate', [Token('PREDICATE_SYMBOL', 'continuantPartOf'), Token('VARIABLE', 'P2'), Token('VARIABLE', 'Q1'), Token('VARIABLE', 'R2')])])]), Tree('disjunction', [Tree('negation', [Tree(Token('RULE', 'predicate'), [Token('PREDICATE_SYMBOL', 'continuantPartOf'), Token('VARIABLE', 'P2'), Token('VARIABLE', 'Q2'), Token('VARIABLE', 'R3')])]), Tree(Token('RULE', 'predicate'), [Token('PREDICATE_SYMBOL', 'continuantPartOf'), Token('VARIABLE', 'P2'), Token('VARIABLE', 'Q2'), Token('VARIABLE', 'S1')])])])])])])])
    # calc = toBoundedMinifiedPCNF().adjust_transform_repeatedly(base)
    # assert calc == ground, f"From black/white should have got green, got red (=string) instead {treeExplainer(base), treeExplainerGREEN(ground), treeExplainerRED(calc), calc}"

    
    # for i in [0,1,2,3,4,5,6,7,8,9]:
    #     print("The tree:")
    #     treeExplainerGREEN(EXAMPLE_ASTS[i])
    #     print("Is correctly transformed into:")
    #     treeExplainerRED((calc:=toBoundedMinifiedPCNF().adjust_transform_repeatedly(EXAMPLE_ASTS[i])))
    #     print("Whose string version is >>>>>>>>>>", ToString().visit(calc))
    #     print("==="*50)
    
    print("All good for bounded minified range co-range form")

def test_range_and_corange_auto():
    tests = [
    ("(exists X all Y lec(Y) -> att(X,Y)).","exists Y att(X,Y).","all Y - lec(Y)."),
    ("(exists X all Y ( - P(X,Y) | Q(X,Y))).","dom(X).","False."),
    # ("(U(V) | (exists X all Y ( - P(X,Y) | Q(X,Y)))).",""),
    ("(all X all Y lec(Y) -> att(X,Y)).","dom(X).","True."),
    # ("(- exists X (B(X) & - - - - att(X,Y))).","",""),
    # ("(all X all Y all Z all T all TAU cP(X,Y,T) & cP(Y,Z,TAU) & tP(T,TAU) -> cP(X,Z,T)).",""),
    # ("all P all Q all R all S  ((((continuantPartOf(P,Q,R)) & (temporalPartOf(S,R)))) -> (continuantPartOf(P,Q,S))) # label(\"continuant-part-of-dissective-on-third-argument-temporal\") .",""),
    # ("all X all T  ((instanceOf(X,fiatLine,T)) -> (exists S exists TP  (((temporalPartOf(TP,T)) & (occupiesSpatialRegion(X,S,TP)) & (instanceOf(S,oneDimensionalSpatialRegion,TP)))))) # label(\"fiat-line-occupies-1d-spatial-regions\") .",""),
    # ("all A all B  ((((exists T  (((instanceOf(A,objectAggregate,T)) & (continuantPartOf(A,B,T)) & (continuantPartOf(B,A,T))))) & (all T  ((continuantPartOf(A,B,T)) <-> (continuantPartOf(B,A,T)))))) -> ((A) = (B))).",""),
    # ("all P all C1 all C2  ((((occursIn(P,C1)) & (all T  ((eXistsAt(P,T)) <-> (locatedIn(C1,C2,T)))))) -> (occursIn(P,C2))).",""),
    # ("(exists X all Y ((A(X,Y) | B(X,Y)) & (C(X,Y) | D(Y)) & (E(Y) | F(Y)))).",""),
    # ("(exists X all Y ((A(X,Y) | B(X,Y)) & (C(X,Y) | D(Y)))).",""),
    # ("(exists X all Y (A(X,Y) & (C(X,Y) | D(Y)))).",""),
    ]
    test_with_parsing(tests = [(x,y) for x,y,z in tests], func = lambda x: get_range_corange_auto(x,False)[0], name = "range", postprocess=RemoveLines())
    test_with_parsing(tests = [(x,z) for x,y,z in tests], func = lambda x: get_range_corange_auto(x,False)[1], name = "corange", postprocess=RemoveLines())
    
    try: 
        GetRange()(prover9_parser.parse("(att(X,Y))."))
    except TypeError:
        print("Got TypeError when it should happen")


    print("All good with range and corange!")


if __name__ == "__main__":
    showcase_bond_evaluation()
    
    test_satisfies_equalities()
    test_range_and_bounded_minification()
    test_range_and_corange_auto()

    