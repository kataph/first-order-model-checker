from typing import Any
from model import Model

from lark import Tree, Transformer
from lark.visitors import Visitor


def swap(term: tuple[Any], c1: Any, c2) -> tuple[Any]:
    """Given a tuple and two of its terms, it returns the same tuple with the terms swapped. Note that if the tuple does not contain the terms the 
    same tuple is returned. If only one of the two terms is present, only that one is replaced.
        For example, swap((1,2,3), 1, 2) -> (2,1,3), swap((1,0,3), 1, 2) -> (2,0,3), swap((0,0,3), 1, 2) -> (0,0,3)"""
    
    if c1 == c2: 
        return term
    
    if (not c1 in term) and (not c2 in term):
        return term

    swapped = list(term)
    for idx, element in enumerate(term):
        if element == c1:
            swapped[idx] = c2
        if element == c2:
            swapped[idx] = c1
    return tuple(swapped)

def test_swap():
    assert swap((1,2,3), 1, 1) == (1,2,3); print("swap((1,2,3), 1, 1) == (1,2,3) OK")
    assert swap((1,2,3), 1, 2) == (2,1,3); print("swap((1,2,3), 1, 2) == (2,1,3) OK")
    assert swap((1,0,3), 1, 2) == (2,0,3); print("swap((1,0,3), 1, 2) == (2,0,3) OK")
    assert swap((0,0,3), 1, 2) == (0,0,3); print("swap((0,0,3), 1, 2) == (0,0,3) OK")
    
def find_equivalent(terms: list[tuple[Any]], model: Model) -> list[set[Any]]: 
    """Given the terms linked to a predicate the equivalent classes of constants w.r.to that predicate are returned. It includes the singleton classes. 
        For example, given {(1,2,3), (1,3,2), (2,2,2), (3,3,3)} from a model with {1,2,3,4,5} as constants, the three {{1}, {2,3}, {4,5}} equivalence classes are returned"""
    
    # first checks that the tuples in the set all have the same arity
    arities = {len(t) for t in terms}
    if len(arities) != 1: raise AssertionError(f"I've received tuples with the wrong arities: the arities are {arities}, while there should be just one arity")
    arity = arities.pop()

    constants = model.signature.constants.copy()
    constants.sort() # now constants is increasing

    if arity == 1: 
        positive_class = {term[0] for term in terms}
        negative_class = set(constants).difference(positive_class)
        return [positive_class, negative_class]
    
    # arity now is > 1:
    couples = {}
    for constant1 in constants:
        for constant2 in constants:
            if constant1 == constant2:
                continue
            couples.update({(constant1, constant2): True})
            for term in terms:
                swapped = swap(term, constant1, constant2)
                if swapped != term and swapped not in terms:
                    couples.update({(constant1, constant2): False})
                    break

    couples = {key:value for key, value in couples.items() if value}
    classes = list()
    for couple in couples.keys():
        flag = False
        for fset in classes:
            if couple[0] in fset: 
                fset.add(couple[1])
                flag = True
            if couple[1] in fset: 
                flag = True
                fset.add(couple[0])
        if not flag:
            classes.append(set(couple))
            flag = True

    # adds singletons
    for x in set(model.signature.constants).difference(set().union(*classes)):
        classes.append({x})
            
    return classes

def test_find_equivalent():
    m = Model()
    m.signature.constants = [1,2,3,4,5]
    assert find_equivalent([(1,2,3),(1,3,2),(2,2,2),(3,3,3)], m) == [{2,3}, {4,5}, {1}]; print("find_equivalent([(1,2,3),(1,3,2),(2,2,2),(3,3,3)], m) == [{2,3}, {4,5}, {1}] OK")
    assert find_equivalent([(1,2,3),(2,2,2),(3,3,3)], m) == [{4,5}, {1}, {2}, {3}]; print("find_equivalent([(1,2,3),(2,2,2),(3,3,3)], m) == [{4,5}, {1}, {2}, {3}] OK")
    assert find_equivalent([(1,2,3),(2,2,2),(3,3,3),(4,4,4)], m) == [{1}, {2}, {3}, {4}, {5}]; print("find_equivalent([(1,2,3),(2,2,2),(3,3,3),(4,4,4)], m) == [{1}, {2}, {3}, {4}, {5}] OK")
    assert find_equivalent([(1,3),(2,3)], m) == [{1,2}, {4,5}, {3}]; print("find_equivalent([(1,3),(2,3)], m) == [{1,2}, {4,5}, {3}] OK")

def intersects_equivalence_classes(equivalence_relations: list[list[set[Any]]], model: Model):
    """Given a list of equivalence relations, it returns their intersection (w.r.to. a model supplying a list of common constants).
    E.g. [[{1,2,3},{4,5}],[{1,2},{3},{4,5}]], [1,2,3,4,5] --> [{1, 2}, {3}, {4, 5}]"""
    if len(equivalence_relations) == 0: return []
    intersection_relation = equivalence_relations.pop()
    for equivalence_relation in equivalence_relations:
        new_intersection_relation = []
        for equivalence_class_1 in intersection_relation:
            for equivalence_class_2 in equivalence_relation:
                # print("------------------------------------------->",equivalence_relations)
                # print("------------------------------------------->",equivalence_class_1, equivalence_class_2)
                if len(intersection:=equivalence_class_1.intersection(equivalence_class_2)) > 0:
                    new_intersection_relation.append(intersection)
        intersection_relation = new_intersection_relation
    # adds singletons
    for x in set(model.signature.constants).difference(set().union(*intersection_relation)):
        intersection_relation.append({x})
    return intersection_relation
    

def test_intersects_equivalence_classes():
    m = Model()
    m.signature.constants = [1,2,3,4,5]
    assert intersects_equivalence_classes([[{1,2,3},{4,5}],[{1,2},{3},{4,5}]], m) == [{1, 2}, {3}, {4, 5}]; print("intersects_equivalence_classes([[{1,2,3},{4,5}],[{1,2},{3},{4,5}]], m) == [{1, 2}, {3}, {4, 5}]")
    assert intersects_equivalence_classes([[{1,2,3},{4,5}],[{1,2},{3},{4,5}], [{1,2},{3},{4},{5}]], m) == [{1, 2}, {3}, {4}, {5}]; print("intersects_equivalence_classes([[{1,2,3},{4,5}],[{1,2},{3},{4,5}], [{1,2},{3},{4},{5}]], m) == [{1, 2}, {3}, {4}, {5}]")
    assert intersects_equivalence_classes([[{1,2,3},{4,5}],[{1,2}]], m) == [{1, 2}, {3}, {4}, {5}]; print("intersects_equivalence_classes([[{1,2,3},{4,5}],[{1,2}]], m) == [{1, 2}, {3}, {4}, {5}]")

if __name__ == "__main__":
    # test_swap()
    # test_find_equivalent()
    # test_intersects_equivalence_classes()
    # s()
    pass