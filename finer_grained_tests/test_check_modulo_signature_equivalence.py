# Remember to execute this file in e.g. the following way (from the root folder): python -m finer_grained_tests.test_check_modulo_signature_equivalence
from model import prover9_parser
from check_modulo_signature_equivalence import *

def test_swap():
    assert swap((1,2,3), 1, 1) == (1,2,3); print("swap((1,2,3), 1, 1) == (1,2,3) OK")
    assert swap((1,2,3), 1, 2) == (2,1,3); print("swap((1,2,3), 1, 2) == (2,1,3) OK")
    assert swap((1,0,3), 1, 2) == (2,0,3); print("swap((1,0,3), 1, 2) == (2,0,3) OK")
    assert swap((0,0,3), 1, 2) == (0,0,3); print("swap((0,0,3), 1, 2) == (0,0,3) OK")

def test_find_equivalent():
    m = Model()
    m.signature.constants = [1,2,3,4,5]
    assert find_equivalent([(1,2,3),(1,3,2),(2,2,2),(3,3,3)], m) == [{2,3}, {4,5}, {1}]; print("find_equivalent([(1,2,3),(1,3,2),(2,2,2),(3,3,3)], m) == [{2,3}, {4,5}, {1}] OK")
    assert find_equivalent([(1,2,3),(2,2,2),(3,3,3)], m) == [{4,5}, {1}, {2}, {3}]; print("find_equivalent([(1,2,3),(2,2,2),(3,3,3)], m) == [{4,5}, {1}, {2}, {3}] OK")
    assert find_equivalent([(1,2,3),(2,2,2),(3,3,3),(4,4,4)], m) == [{1}, {2}, {3}, {4}, {5}]; print("find_equivalent([(1,2,3),(2,2,2),(3,3,3),(4,4,4)], m) == [{1}, {2}, {3}, {4}, {5}] OK")
    assert find_equivalent([(1,3),(2,3)], m) == [{1,2}, {4,5}, {3}]; print("find_equivalent([(1,3),(2,3)], m) == [{1,2}, {4,5}, {3}] OK")

def test_intersects_equivalence_classes():
    m = Model()
    m.signature.constants = [1,2,3,4,5]
    assert intersects_equivalence_classes([[{1,2,3},{4,5}],[{1,2},{3},{4,5}]], m) == [{1, 2}, {3}, {4, 5}]; print("intersects_equivalence_classes([[{1,2,3},{4,5}],[{1,2},{3},{4,5}]], m) == [{1, 2}, {3}, {4, 5}] OK")
    assert intersects_equivalence_classes([[{1,2,3},{4,5}],[{1,2},{3},{4,5}], [{1,2},{3},{4},{5}]], m) == [{1, 2}, {3}, {4}, {5}]; print("intersects_equivalence_classes([[{1,2,3},{4,5}],[{1,2},{3},{4,5}], [{1,2},{3},{4},{5}]], m) == [{1, 2}, {3}, {4}, {5}] OK")
    assert intersects_equivalence_classes([[{1,2,3},{4,5}],[{1,2}]], m) == [{1, 2}, {3}, {4}, {5}]; print("intersects_equivalence_classes([[{1,2,3},{4,5}],[{1,2}]], m) == [{1, 2}, {3}, {4}, {5}] OK")


if __name__ == "__main__":
    test_swap()
    test_find_equivalent()
    test_intersects_equivalence_classes()
    