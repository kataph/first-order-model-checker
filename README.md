## Model Checker For First-Order Logic
This is a model checker for first-order logic. That is, given a model and a theory, it is checked that the model satisfies the theory. 
The model is supplied as a list of assertions, with the convention that each and every true assertion is stated and each and every false assertion is not stated. 
The theory is supplied as a list of axioms. 

The syntax is similar to that of [Prover9][https://www.cs.unm.edu/~mccune/mace4/].

The algorithm is a simple brute force approach that evaluates all axioms sequentially. If an axioms is false the algorithm stops and explains why the axioms was evaluated false. 

Simply run check.py supplying the path to a file containing a model and the path to a file containing a theory (e.g. `>python check.py DOLCE-clay-statue-model.p9 DOLCE-clay-statue-axioms.p9`).
Some tests are present in `tests.py`. They can be run by executing that file. The `DOLCE-clay-statue` model and axioms files are an example of model and theory files, as well as an additional tests.

Note that the complexity of the algorithm is O(c^a) where c is the number of constants in the model, and a is the maximum nesting-depth of quantifiers.   

## TODOS
- Implement faster strategies in addition to brute force. 
- Implement simplified treatment for defined predicates.
- Implement functions.

## Some Finer Details
- The syntax is similar to prover9. However, *functions are not implemented* (except for constant symbols). Additionally, the `!=` operator is not implemented, and the default prover9 operator priority has been hardcoded in the grammar and cannot be changed. 
- Note that the model is specified following a closed-world-style convention. 
- Equality is not implemented in the model specification: it is assumed that differently named constants are different; and that all the constant that exist in the model are exactly those mentioned in some assertion.  
- The algorithm is not "smart": e.g. `all X0 all X1 all X2 ... all X100 phi | - phi` is a tautology but will not be evaluated. Additionally, defined predicates are
- Explanation works by visiting an axiom parsing tree and specifying for each node its truth value for the relevant variables substitutions. 