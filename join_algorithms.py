from functools import partial
from time import perf_counter
from typing import Any

class Relation():
    def __init__(self, tuple_header: tuple[str], tuple_set: set[tuple[Any]] | bool):
        """tuple set can be a boolean (for zero-arity relations)"""
        self.tuple_header = tuple_header
        self.tuple_set = tuple_set
    def __str__(self):
        if self.tuple_header == ():
            return f"Nullary relation with value {self.tuple_set}"
        return f"Relation about variables {self.tuple_header}. The first 3 tuples (if more than 3, otherwise all) are {self.tuple_set if len(self.tuple_set) <= 3 else list(self.tuple_set)[0:3]}"

def control_if_join_is_proper(header1, header2, keys) -> tuple[list[int], list[int], list[int], list[int], tuple]:
    """Given the headers and common keys of a join, controls if a join is proper. If it isnt, raises an error. If it is, it returns index of shared and non-shared keys for both headers,
    as well as the join header, in the following order: key_indices1, key_indices2, not_key_indices1, not_key_indices2, join_header"""
    seen = set()
    duplicated_keys = {x for x in keys if x in seen or seen.add(x)} # note that this work only with hashables
    if len(duplicated_keys) > 0 :
        raise TypeError(f"No duplicates in the keys!")

    if not (all(key in header1 for key in keys) and all(key in header2 for key in keys)):
        raise TypeError(f"I am considering only proper joins where all keys are shared by both relation")
    
    if (set(header1) == set(keys) or set(header2) == keys):
        print(f"WARNING: >>>>A join is being execute, where the columns of a relation are subset of the other: {header1} and {header2}. A simple intersection should be probably executed instead<<<<")

    key_indices1 = [header1.index(key) for key in keys]
    key_indices2 = [header2.index(key) for key in keys]
    not_key_indices1 = [i for i, var in enumerate(header1) if var not in keys]
    not_key_indices2 = [i for i, var in enumerate(header2) if var not in keys]


    if len(key_indices1) != len(key_indices2):
        raise TypeError(f"Something went wrong! The length of the indices should be the same, equal to len({keys})")
    
    join_header = tuple(var for var in header1 if var not in keys) + keys + tuple(var for var in header2 if var not in keys)
    return key_indices1, key_indices2, not_key_indices1, not_key_indices2, join_header

def all_keys_are_shared(key_indices1, key_indices2, keys, t1, t2) -> bool:
    if len(keys) == 1:
        return t1[key_indices1[0]] == t2[key_indices2[0]]
    if len(keys) == 2:
        return t1[key_indices1[0]] == t2[key_indices2[0]] and t1[key_indices1[1]] == t2[key_indices2[1]]
    return all(t1[i] == t2[j] for i,j in zip(key_indices1,key_indices2))
def merge_jointed_tuples(key_indices1, t1, t2, not_key_indices1, not_key_indices2) -> tuple:
    """Given two tuple that have the same key values, a tuple is returned that contains all elements of both tuples: first the non-key elements of the first tuple, then the (de-duplicated) key elements, then the non-key elements of the second tuple"""
    t1_minus_keys = tuple(t1[i] for i in not_key_indices1)
    t2_minus_keys = tuple(t2[i] for i in not_key_indices2)
    de_duplicated_keys = tuple(t1[i] for i in key_indices1)
    return t1_minus_keys + de_duplicated_keys + t2_minus_keys
def get_key_from_tuple(t: tuple, key_indices: dict) -> tuple:
    return tuple(t[i] for i in key_indices)


def simple_nested_loops_join(r1: set[tuple], key_idx1, r2:set[tuple], key_idx2) -> set[tuple]:
    ro = set()
    for t1 in r1:
        for t2 in r2:
            if t1[key_idx1] == t2[key_idx2]:
                ro.add((t1[0], t1[1], t2[1]))
    return ro

def intersection_join(r1: Relation, r2: Relation) -> Relation:
    """The special case that the variables of one relation are subset of the variables of the other: a simple intersection is executed"""
    if set(r1.tuple_header).issubset(set(r2.tuple_header)):
        small_rel = r1
        big_rel = r2
    elif set(r2.tuple_header).issubset(set(r1.tuple_header)):
        small_rel = r2
        big_rel = r1
    else:
        raise TypeError("the variables of one relation are not subset of the variables of the other. This function should not be called in this case!")
    
    join_relation = Relation(tuple_header=big_rel.tuple_header, tuple_set=set())
    deduped_indices_of_big_that_are_in_small = [big_rel.tuple_header.index(var) for var in small_rel.tuple_header]
    for t in big_rel.tuple_set:
        if tuple(t[i] for i in deduped_indices_of_big_that_are_in_small) in small_rel.tuple_set:
            join_relation.tuple_set.add(t)
    return join_relation

def nested_loops_join(r1: Relation, r2: Relation, keys: tuple[str]) -> Relation: # <-- more than 10 times slower than simple version...
    header1 = r1.tuple_header
    header2 = r2.tuple_header
    key_indices1, key_indices2, not_key_indices1, not_key_indices2, join_header = control_if_join_is_proper(header1, header2, keys)
    
    join_relation = Relation(tuple_header=join_header, tuple_set=set())
    for t1 in r1.tuple_set:
        for t2 in r2.tuple_set:
            # if all_keys_are_shared(key_indices1, key_indices2, keys, t1, t2): # <-- This is more readable but it kills performance (X5)
            if len(keys) == 1:
                flag = t1[key_indices1[0]] == t2[key_indices2[0]]
            else:
                flag = all(t1[i] == t2[j] for i,j in zip(key_indices1,key_indices2))
            if flag:
                join_relation.tuple_set.add(merge_jointed_tuples(key_indices1, t1, t2, not_key_indices1, not_key_indices2))
    return join_relation

def merge_sort_join_1(r1: Relation, r2: Relation, keys: tuple[str]) -> Relation:
    """Merge sort taken from wikipedia (https://it.wikipedia.org/wiki/Sort_merge_join)"""
    header1 = r1.tuple_header
    header2 = r2.tuple_header
    key_indices1, key_indices2, not_key_indices1, not_key_indices2, join_header = control_if_join_is_proper(header1, header2, keys)

    sr1 = sorted(r1.tuple_set, key=partial(get_key_from_tuple, key_indices = key_indices1))
    sr2 = sorted(r2.tuple_set, key=partial(get_key_from_tuple, key_indices = key_indices2))
    join_relation = Relation(tuple_header=join_header, tuple_set=set())
    idx1 = 0
    idx2 = 0
    while idx1<len(sr1) and idx2<len(sr2): 

        key1 = get_key_from_tuple(sr1[idx1], key_indices1)
        key2 = get_key_from_tuple(sr2[idx2], key_indices2)

        if key1 > key2:
            idx2 += 1

        elif key1 < key2:
            idx1 += 1

        else:
            join_relation.tuple_set.add(merge_jointed_tuples(key_indices1, sr1[idx1], sr2[idx2], not_key_indices1, not_key_indices2))
            
            idx1_t = idx1 
            while idx1_t+1<len(sr1) and get_key_from_tuple(sr1[idx1_t+1], key_indices1) == get_key_from_tuple(sr2[idx2], key_indices2):
                join_relation.tuple_set.add(merge_jointed_tuples(key_indices1, sr1[idx1_t+1], sr2[idx2], not_key_indices1, not_key_indices2))
                idx1_t+=1

            idx2_t = idx2 
            while idx2_t+1<len(sr2) and get_key_from_tuple(sr1[idx1], key_indices1) == get_key_from_tuple(sr2[idx2_t+1], key_indices2):
                join_relation.tuple_set.add(merge_jointed_tuples(key_indices1, sr1[idx1], sr2[idx2_t+1], not_key_indices1, not_key_indices2))
                idx2_t+=1
            
            idx1+=1
            idx2+=1
    return join_relation

def merge_sort_join_2(r1: Relation, r2: Relation, keys: tuple[str]) -> Relation:
    """Merge sort, uses nested loops join when joining subset of relations sharing the same key"""
    header1 = r1.tuple_header
    header2 = r2.tuple_header
    key_indices1, key_indices2, not_key_indices1, not_key_indices2, join_header = control_if_join_is_proper(header1, header2, keys)
    
    sr1 = sorted(r1.tuple_set, key=partial(get_key_from_tuple, key_indices = key_indices1))
    sr2 = sorted(r2.tuple_set, key=partial(get_key_from_tuple, key_indices = key_indices2))
    join_relation = Relation(tuple_header=join_header, tuple_set=set())
    idx1 = 0
    idx2 = 0
    key1 = get_key_from_tuple(sr1[idx1], key_indices1)
    key2 = get_key_from_tuple(sr2[idx2], key_indices2)
    while True:
        if key1 == key2: 
            sec1_idx_str = idx1
            # sec1_idx_end = next(i for i,v in enumerate(sr1) if i+1 == len(sr1) or sr1[i+1][key_idx1] > key1) # <-- unacceptable: it raises the complexity too much
            sec1_idx_end = sec1_idx_str 
            while sec1_idx_end+1 < len(sr1) and get_key_from_tuple(sr1[sec1_idx_end+1], key_indices1) == key1:
                sec1_idx_end += 1
            section1 = sr1[sec1_idx_str:sec1_idx_end+1]
            sec2_idx_str = idx2
            # sec2_idx_end = next(i for i,v in enumerate(sr2) if i+1 == len(sr2) or sr2[i+1][key_idx2] > key2) # <-- unacceptable: it raises the complexity too much
            sec2_idx_end = sec2_idx_str 
            while sec2_idx_end+1 < len(sr2) and get_key_from_tuple(sr2[sec2_idx_end+1], key_indices2) == key2:
                sec2_idx_end += 1
            section2 = sr2[sec2_idx_str:sec2_idx_end+1]

            # sro = sro.union(nested_loops_join(section1,key_idx1,section2,key_idx2)) # <-- unacceptable: it raises the complexity too much
            for t1 in section1:
                for t2 in section2:
                    join_relation.tuple_set.add(merge_jointed_tuples(key_indices1, t1, t2, not_key_indices1, not_key_indices2))

            if sec1_idx_end+1==len(sr1) or sec2_idx_end+1==len(sr2): break
            idx1 = sec1_idx_end+1
            idx2 = sec2_idx_end+1
            key1 = get_key_from_tuple(sr1[idx1], key_indices1)
            key2 = get_key_from_tuple(sr2[idx2], key_indices2)
        elif key1 < key2: # also just if, but clearer this way
            if idx1+1==len(sr1): break
            idx1 += 1
            key1 = get_key_from_tuple(sr1[idx1], key_indices1)
        elif key1 > key2:
            if idx2+1==len(sr2): break
            idx2 += 1
            key2 = get_key_from_tuple(sr2[idx2], key_indices2)
    return join_relation

def hash_join(r1: Relation, r2: Relation, keys: tuple[str]) -> Relation:
    header1 = r1.tuple_header
    header2 = r2.tuple_header
    key_indices1, key_indices2, not_key_indices1, not_key_indices2, join_header = control_if_join_is_proper(header1, header2, keys)
    
    join_relation = Relation(tuple_header=join_header, tuple_set=set())
    
    hash_table = dict()
    for t2 in r2.tuple_set:
        # key2 = get_key_from_tuple(t2, key_indices2, keys) #<- slight loss in performance
        key2 = tuple(t2[i] for i in key_indices2)
        if not key2 in hash_table:
            hash_table[key2] = set()
            hash_table[key2].add(t2)
        else:
            hash_table[key2].add(t2)
    
    for t1 in r1.tuple_set:
        key1 = tuple(t1[i] for i in key_indices1)
        # key1 = get_key_from_tuple(t1, key_indices1, keys) #<- slight loss in performance
        if not key1 in hash_table:
            continue
        else:
            for t2 in hash_table[key1]:
                join_relation.tuple_set.add(merge_jointed_tuples(key_indices1, t1, t2, not_key_indices1, not_key_indices2)) #<- 10x loss in performance w.r.to pass instruction
    return join_relation

def simple_hash_join(r1, key_idx1, r2, key_idx2) -> set[tuple]:
    hro = set()
    
    hash_table = dict()
    for t2 in r2:
        key2 = t2[key_idx2]
        if not key2 in hash_table:
            hash_table[key2] = set()
            hash_table[key2].add(t2)
        else:
            hash_table[key2].add(t2)
    
    for t1 in r1:
        key1 = t1[key_idx1]
        if not key1 in hash_table:
            continue
        else:
            for t2 in hash_table[key1]:
                hro.add((t1[0],t1[1],t2[1]))
    return hro

def add_counter(func):
    def wrapper(*args, **kwargs):
        s = perf_counter()
        out = func(*args, **kwargs)
        e = perf_counter()
        print(f"Execution time of {func.__name__}: {e-s}")
        return out
    return wrapper