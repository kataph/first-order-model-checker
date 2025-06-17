# Remember to execute this file in e.g. the following way (from the root folder): python -m finer_grained_tests.test_and_benchmark_check

from check import *

def test_signature_extraction():
    p9sig = P9SignatureExtractor()
    assert p9sig.transform(prover9_parser.parse("all X exists Y P(X,Y) & X=Y .")) == {'=', 'P'}; print("""p9sig.transform(prover9_parser.parse("all X exists Y P(X,Y) & X=Y .")) == {'=', 'P'}""")
    assert p9sig.transform(prover9_parser.parse("((all X exists Y P(X,Y) & X=Y) | (exists X exists Z all U all V (E(X,y,Z) & R(U,V)))) .")) == {'=', 'P', 'E', 'R'}; print("""p9sig.transform(prover9_parser.parse("((all X exists Y P(X,Y) & X=Y) | (exists X exists Z all U all V (E(X,y,Z) & R(U,V)))) .")) == {'=', 'P', 'E', 'R'}""")
    assert p9sig.transform(prover9_parser.parse("all X all Y P(X) & Q(Y) .")) == {'P', 'Q'}; print("""p9sig.transform(prover9_parser.parse("all X all Y P(X) & Q(Y) .")) == {'P', 'Q'}""")
    print("All good for signature extraction")

def benchmark_check_algorithm():
    print("Starting to benchmark some strategies")
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
        o2 = add_counter_with_options(check_lines)(axioms, model, options = ["equivalence"], timeout = 20, timeout_aux = 20, no_timeout = False, breakOnFalse = True)
        o3 = add_counter_with_options(check_lines)(axioms, model, options = ["range"], timeout = 20, timeout_aux = 20, no_timeout = False, breakOnFalse = True)
        o4 = add_counter_with_options(check_lines)(axioms, model, options = ["equivalence","range"], timeout = 20, timeout_aux = 20, no_timeout = False, breakOnFalse = True)
        print("\n",o2,"\n",o3,"\n",o4) #print("\n",o1,"\n",o2,"\n",o3,"\n",o4)
    for i in range(10):
        model_txt += f"cP(x{i},y{i},t{i}).cP(y{i},z{i},tau{i}).tP(t{i},tau{i}).cP(x{i},z{i},t{i})."
        model = P9ModelReader().read_model(prover9_parser.parse(model_txt))
        print(f"Working with model with constants: {model.signature.constants}")
        #o1 = add_counter_with_options(check_lines)(axioms, model, options = []) <- this explodes soon
        # o2 = add_counter_with_options(check_lines)(axioms, model, options = ["equivalence"]) <- this also explodes in this case
        o3 = add_counter_with_options(check_lines)(axioms, model, options = ["range"], timeout = 20, timeout_aux = 20, no_timeout = False, breakOnFalse = True)
        o4 = add_counter_with_options(check_lines)(axioms, model, options = ["equivalence","range"], timeout = 20, timeout_aux = 20, no_timeout = False, breakOnFalse = True)
        print("\n",o3,"\n",o4) #print("\n",o1,"\n",o2,"\n",o3,"\n",o4)

if __name__ == "__main__":
    test_signature_extraction()
    benchmark_check_algorithm()
