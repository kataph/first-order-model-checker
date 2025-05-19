# Model Checker For First-Order Logic
## Introduction
This is a model checker for first-order logic. That is, given a model and a theory, it is checked that the model satisfies the theory. 
The model is supplied as a list of assertions, with the convention that each and every true assertion is stated and each and every false assertion is not stated. 
The theory is supplied as a list of axioms. 

The syntax is similar to that of [Prover9](https://www.cs.unm.edu/~mccune/mace4/) with some caveats (see Finer Detaisl).

As of now three evaluation strategies have been implemented: 
- a simple, nested-loop style brute-force approach that evaluates all axioms sequentially.
- an equivalence-based strategy, that reduces the size of the quantification domain for each quantifier: given the signature of the quantified formula, all the constants that cannot be distinguished by the symbols in the signature are collapsed together. 
- a further reduction of the quantification domains based on the a-priori determination of simple range expressions that the quantified variables must satisfy. Derived on some old works about first-order queries on databases of the 80s-90s (Mainly [this one](https://link.springer.com/chapter/10.1007/3-540-51251-9_8) of François Bry). 

Simply run check.py supplying the path to a file containing a model and the path to a file containing a theory (e.g. `python3 check.py -m DOLCE_p9/DOLCE-clay-statue-model.p9 -a DOLCE_p9/DOLCE-clay-statue-axioms.p9` or `python check.py [...]`). 
Default evaluation strategy is brute force. Supply a value to `--options` (can only be `equivalence` or `range`) to change the evauation strategy. 

Some tests are present in `tests.py`. They can be run by executing that file. 
Further examples are present in the `DOLCE_p9` and `BFO_p9` folders. For instance, the `DOLCE-clay-statue` model and axioms files are an example of model and theory files contained in `DOLCE_p9`. 

Note that the complexity of the brute-force algorithm is `O(c^a)` where `c` is the number of constants in the model, and `a` is the maximum nesting-depth of quantifiers. 
The equivalence strategy reduces this to `O(c'^a)` where `c'` is the number of equivalence classes of constants that can be distinguished by a property formulated with the signature of the underlying axiom (`c'` is typically smaller than `c`, however they are the same in the worst case). It is most impactful if the signature of the axiom is small w.r.to the signature of the whole theory, however, if the signature of the axiom contains equality, the complexity goes back to the brute-force case. 
The range-constraining strategy further reduces the number `c'`, to a quantity that must be evaluated depending on the underlying quantifier in the axiom, and is difficult describe a-priori. Again, in the worst case there is no increase in performance, however, in the typical case, the increment is huge. The range-bounds are relatively simple formulas: at most union of existential conjunctive formulas, that is, they are union of conjunctive queries and the underlying conjunctive queries are evaluated against the model using hash-joins with no non-trivial optimizations. 

## How to install
For now clone or download the repo and execute the python file `check.py`. 
To clone the repo: execute the following line in a terminal `git clone https://github.com/kataph/fol_model_checker.git`.
Then execute the python file `check.py` and supply the correct arguments as explained in the next section. 
Before that, if so needed, install the requirements with e.g. `pip3 install -r requirements.txt` or `pip install -r requirements.txt`. 

## How to use
The input arguments are:
- `-m`, `--model_file`, type: str, Model file location
- `-a`, `--axioms_file`, type: str, Axioms file location
- `-o`, `--options`, type: str, nargs = "+", default: [], Options. Currently only 'equivalence' and 'range' are supported
- `-t`, `--timeout`, type: int, default = 10, Timeout of the chosen strategy, in seconds. After the timeout the auxillary strategy will be called
- `-taux`, `--timeout_aux`, type: int, default: 120, Timeout of the auxillary strategy, in seconds.
- `-nout`, `--no_timeout`, type: bool, default: False, Deactivates the timeout system.
- `-bof`, `--break_on_false`, type: bool, default: True, If true, which is the default value, the program will stop at the first axiom evaluated as False.

The first two arguments are required, the others are options. By default the strategy employed is brute-force. Multiple strategy will result in a mixed behavior which may or may not be more performing than the single strategies by themselves. By default the selected strategy will be executed for the `--timeout` number of seconds, if such a timeout is reached, a default equivalence strategy will be executed for the `--timeout_aux` number of seconds. If there is still a timeout then nothing else is attempted. 
The timeout can be deactivated using the `--no_timeout` option, in which case the selected strategy will run without interruption (possibly forever).
Finally, if multiple axioms are present in the axiom file, and a false axiom is met, the default behavior is stopping the evaluation and supplying an explanation. This can be modified with the `--break_on_false` option: if set to `false`, the program will pass to the next axiom after having met a false axiom.

If a false axiom is met an explanation will be generated and saved to a file. The explanation is constituted by a tree representing the axiom, where each node has a truth value. The truth value of a quantifier is accompanied also by the last set of constants the truth value was verified on before finding the axiom false. 
If multiple false axioms are found, then an explanation for each one will be generated and saved to a different file, numbered with the line number of where the axiom is located in the axioms file. 

## TODOS
- simplify use
- Implement simplified treatment for defined predicates.
- Implement functions.

## Some Finer Details
- The syntax is similar to prover9. However, *functions are not implemented* (except for constant symbols). Additionally, the `!=` operator is not implemented, and the default prover9 operator priority has been hardcoded in the grammar and cannot be changed. 
- Note that the model is specified following a closed-world-style convention. 
- Equality is not implemented in the model specification: it is assumed that differently named constants are different; and that all the constant that exist in the model are exactly those mentioned in some assertion.  
- The algorithm is not "smart": e.g. `all X0 all X1 all X2 ... all X100 phi | - phi` is a tautology but will not be evaluated.
- Explanation works by visiting an axiom parsing tree and specifying for each node its truth value for the relevant variables substitutions. 
