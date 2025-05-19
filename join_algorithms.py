import random

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

def control_if_join_is_proper(header1, header2, keys):
    seen = set()
    duplicated_keys = {x for x in keys if x in seen or seen.add(x)} # note that this work only with hashables
    if len(duplicated_keys) > 0 :
        raise TypeError(f"No duplicates in the keys!")

    if not (all(key in header1 for key in keys) and all(key in header2 for key in keys)):
        raise TypeError(f"I am considering only proper joins where all keys are shared by both relation")
    
    if (set(header1) == set(keys) or set(header2) == keys):
        # raise TypeError(f"I am considering only proper joins where the columns of a relation are not subset of the other")
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

def intersection_join(r1: Relation, r2: Relation):
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

def nested_loops_join(r1: Relation, r2: Relation, keys: tuple[str]): # <-- more than 10 times slower than simple version...
    header1 = r1.tuple_header
    header2 = r2.tuple_header
    key_indices1, key_indices2, not_key_indices1, not_key_indices2, join_header = control_if_join_is_proper(header1, header2, keys)
    
    # zipped_indices = zip(actual_key_indices1, actual_key_indices2)
    # zipped_indices = [(i,j) for i,j in zip(actual_key_indices1, actual_key_indices2)]


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

def merge_sort_join_wikipedia(r1: Relation, r2: Relation, keys: tuple[str]):
    """Merge sort taken from wikipedia (https://it.wikipedia.org/wiki/Sort_merge_join)"""
    header1 = r1.tuple_header
    header2 = r2.tuple_header
    key_indices1, key_indices2, not_key_indices1, not_key_indices2, join_header = control_if_join_is_proper(header1, header2, keys)

    sr1 = sorted(r1.tuple_set, key=partial(get_key_from_tuple, key_indices = key_indices1))
    sr2 = sorted(r2.tuple_set, key=partial(get_key_from_tuple, key_indices = key_indices2))
    join_relation = Relation(tuple_header=join_header, tuple_set=set())
    idx1 = 0
    idx2 = 0
    # key1 = get_key_from_tuple(sr1[idx1], key_indices1, keys)
    # key2 = get_key_from_tuple(sr1[idx1], key_indices2, keys)
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

def merge_sort_join(r1: Relation, r2: Relation, keys: tuple[str]):
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

def simple_hash_join(r1, key_idx1, r2, key_idx2):
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

def check_and_benchmark_intersection_join():
    in_out_relations = [
        (Relation(("X"),{(1,), (2,), (3,)}),Relation(("X", "Y"),{(1,2), (2,3), (3,4), (5,6), (7,8)}),Relation(("X", "Y"),{(1,2), (2,3), (3,4)})),
        (Relation(("X", "Y"),{(1,1), (2,3), (3,2)}),Relation(("X", "Z", "Y"),{(1,9,1), (2,8,3), (2,3,4)}),Relation(("X", "Z", "Y"),{(1,9,1), (2,8,3)})),
        ]
    for r1, r2, join in in_out_relations:
        assert join.tuple_set == intersection_join(r1,r2).tuple_set
    
    for len1, len2, size in [(100,150,200),(1000,1500,200),(2000,3000,400),(4000,6000,500), (150,100,200),(1500,1000,200),(3000,2000,400),(6000,4000,500)]:
        print(len1, len2, size)
        r1 = Relation(("X"),{(random.randint(1,size),) for x in range(len1)})
        r2 = Relation(("X", "Y"), {(random.randint(1,size),random.randint(1,size)) for x in range(len2)})
        print("len(r1): ", len(r1.tuple_set), "len1: ", len1) 
        print("len(r2): ", len(r2.tuple_set), "len2: ", len2) 
        join_rel = add_counter(intersection_join)(r1,r2)
        print(f"Join = {join_rel}")
        print(f"Join length = {len(join_rel.tuple_set)}")

    print("All good for intersection join")
    
def check_join_algorithms():
    test_tuple_sets = [
    (   
        {(1,1)},
        {(1,12)},
    ),
        ({
        (1,2),
    },
    {
        (2,2),
        (2,11),
        (1,11)
    }),
        ({
        (1,2),
        (3,3),
    },
    {
        (2,2),
        (2,11),
        (1,11)
    }),
        ({
        (1,6),
    },
    {
        (2,2),
    }),
        ({
        (1,2),
    },
    {
        (2,2),
        (2,3),
    }),
        ({
        (1,2),
        (3,2),
        (11,32),
        (4,5),
        (3,3),
        (2,3),
        (4,6),
        (1,6),
    },
    {
        (2,2),
        (3,2),
        (11,32),
        (6,5),
        (6,3),
        (2,3),
        (4,6),
        (1,6),
        (3,9),
        (2,11),
        (1,11)
    }),
    ({
        (1,1)
    },
    {
        (1,1)
    }),
    ({
        (1,2)
    },
    {
        (1,1)
    }),
    ({
        (1,1),
        (2,1),
        (3,1),
        (1,2),
        (2,2),
        (3,2),
    },
    {
        (1,1),
    }),
    ({
        (1,1),
        (2,1),
        (1,2),
        (2,2),
    },
    {
        (1,1),
        (1,2),
        (2,1),
        (2,2),
    }),
    (
        {(142, 180), (1, 30), (181, 107), (151, 45), (82, 46), (85, 8), (196, 16), (183, 180), (156, 7), (167, 83), (147, 196), (31, 67), (142, 191), (20, 94), (197, 181), (15, 116), (127, 156), (63, 129), (146, 154), (197, 165), (80, 25), (26, 173), (70, 143), (26, 118), (165, 14), (159, 193), (180, 179), (113, 43), (90, 50), (102, 24), (64, 159), (117, 107), (36, 115), (188, 121), (117, 79), (130, 43), (116, 62), (87, 35), (110, 30), (101, 134), (9, 146), (63, 190), (33, 103), (175, 86), (107, 125), (142, 156), (48, 112), (77, 38), (150, 16), (41, 127), (53, 92), (101, 56), (137, 189), (149, 35), (24, 77), (161, 64), (175, 8), (184, 75), (197, 166), (162, 56), (64, 30), (28, 193), (10, 13), (109, 1), (5, 163)},
        {(92, 4), (60, 173), (33, 192), (179, 191), (185, 51), (156, 134), (105, 98), (147, 131), (1, 141), (46, 30), (160, 168), (64, 44), (72, 176), (25, 126), (56, 104), (103, 185), (56, 177), (21, 58), (40, 135), (172, 71), (89, 183), (87, 131), (159, 83), (51, 55), (18, 141), (90, 102), (44, 169), (55, 199), (141, 150), (52, 127), (137, 52), (25, 9), (52, 38), (94, 53), (67, 2), (144, 66), (44, 107), (142, 23), (190, 81), (131, 59), (33, 189), (83, 138), (155, 90), (156, 67), (8, 80), (158, 104)}
    ),
    (
        {(142, 180), (1, 30), (181, 107), (151, 45), (82, 46), (85, 8), (196, 16), (183, 180), (156, 7), (167, 83), (147, 196), (31, 67), (142, 191), (20, 94), (197, 181), (15, 116), (127, 156), (63, 129), (146, 154), (197, 165), (80, 25), (26, 173), (70, 143), (26, 118), (165, 14), (159, 193), (180, 179), (113, 43), (90, 50), (102, 24), (64, 159), (117, 107), (36, 115), (188, 121), (117, 79), (130, 43), (116, 62), (87, 35), (110, 30), (101, 134), (9, 146), (63, 190), (33, 103), (175, 86), (107, 125), (142, 156), (48, 112), (77, 38), (150, 16), (41, 127), (53, 92), (101, 56), (137, 189), (149, 35), (24, 77), (161, 64), (175, 8), (184, 75), (197, 166), (162, 56), (64, 30), (28, 193), (10, 13), (109, 1), (5, 163)},
        {(124, 142), (97, 112), (101, 128), (88, 195), (102, 166), (85, 49), (195, 113), (75, 176), (105, 3), (104, 102), (150, 163), (84, 172), (18, 178), (99, 142), (171, 39), (185, 56), (79, 148), (49, 77), (86, 16), (137, 98), (51, 3), (32, 118), (101, 59), (56, 100), (163, 19), (119, 49), (147, 129), (197, 23), (147, 83), (58, 112), (128, 198), (134, 129), (92, 4), (60, 173), (33, 192), (179, 191), (185, 51), (156, 134), (105, 98), (147, 131), (1, 141), (46, 30), (160, 168), (64, 44), (72, 176), (25, 126), (56, 104), (103, 185), (56, 177), (21, 58), (40, 135), (172, 71), (89, 183), (87, 131), (159, 83), (51, 55), (18, 141), (90, 102), (44, 169), (55, 199), (141, 150), (52, 127), (137, 52), (25, 9), (52, 38), (94, 53), (67, 2), (144, 66), (44, 107), (142, 23), (190, 81), (131, 59), (33, 189), (83, 138), (155, 90), (156, 67), (8, 80), (158, 104)}
    ),
    (
        {(98, 37), (97, 17), (105, 61), (42, 57), (187, 121), (157, 16), (110, 29), (47, 199), (168, 80), (58, 150), (19, 146), (141, 47), (122, 76), (6, 75), (164, 94), (127, 191), (10, 127), (67, 27), (140, 29), (43, 160), (6, 141), (104, 155), (20, 15), (65, 47), (156, 37), (14, 17), (120, 53), (55, 54), (117, 5), (77, 5), (3, 10), (182, 195), (97, 117), (87, 6), (108, 93), (142, 180), (1, 30), (181, 107), (151, 45), (82, 46), (85, 8), (196, 16), (183, 180), (156, 7), (167, 83), (147, 196), (31, 67), (142, 191), (20, 94), (197, 181), (15, 116), (127, 156), (63, 129), (146, 154), (197, 165), (80, 25), (26, 173), (70, 143), (26, 118), (165, 14), (159, 193), (180, 179), (113, 43), (90, 50), (102, 24), (64, 159), (117, 107), (36, 115), (188, 121), (117, 79), (130, 43), (116, 62), (87, 35), (110, 30), (101, 134), (9, 146), (63, 190), (33, 103), (175, 86), (107, 125), (142, 156), (48, 112), (77, 38), (150, 16), (41, 127), (53, 92), (101, 56), (137, 189), (149, 35), (24, 77), (161, 64), (175, 8), (184, 75), (197, 166), (162, 56), (64, 30), (28, 193), (10, 13), (109, 1), (5, 163)},
        {(101, 24), (22, 188), (184, 77), (36, 71), (93, 123), (5, 65), (100, 147), (134, 158), (80, 95), (6, 11), (158, 51), (27, 107), (143, 126), (70, 2), (172, 95), (51, 192), (129, 139), (96, 17), (35, 10), (50, 148), (131, 200), (20, 177), (18, 3), (146, 15), (41, 154), (72, 132), (154, 31), (141, 131), (22, 3), (188, 17), (14, 136), (200, 183), (161, 54), (44, 24), (167, 79), (106, 136), (176, 100), (28, 119), (101, 167), (108, 63), (193, 97), (162, 128), (48, 179), (149, 91), (130, 87), (113, 199), (133, 67), (62, 25), (1, 158), (170, 95), (46, 157), (151, 54), (22, 80), (97, 28), (123, 166), (41, 188), (189, 175), (146, 67), (195, 136), (70, 93), (33, 19), (184, 124), (176, 150), (27, 179), (94, 114), (108, 113), (106, 24), (84, 33), (84, 152), (132, 6), (124, 142), (97, 112), (101, 128), (88, 195), (102, 166), (85, 49), (195, 113), (75, 176), (105, 3), (104, 102), (150, 163), (84, 172), (18, 178), (99, 142), (171, 39), (185, 56), (79, 148), (49, 77), (86, 16), (137, 98), (51, 3), (32, 118), (101, 59), (56, 100), (163, 19), (119, 49), (147, 129), (197, 23), (147, 83), (58, 112), (128, 198), (134, 129), (92, 4), (60, 173), (33, 192), (179, 191), (185, 51), (156, 134), (105, 98), (147, 131), (1, 141), (46, 30), (160, 168), (64, 44), (72, 176), (25, 126), (56, 104), (103, 185), (56, 177), (21, 58), (40, 135), (172, 71), (89, 183), (87, 131), (159, 83), (51, 55), (18, 141), (90, 102), (44, 169), (55, 199), (141, 150), (52, 127), (137, 52), (25, 9), (52, 38), (94, 53), (67, 2), (144, 66), (44, 107), (142, 23), (190, 81), (131, 59), (33, 189), (83, 138), (155, 90), (156, 67), (8, 80), (158, 104)}
    ),
    ]
    key_idx1 = 1
    key_idx2 = 0
    keys = ("Z",)
    header1 = ("X", "Z")
    header2 = ("Z", "Y")
    for r1,r2 in test_tuple_sets:
        snro = simple_nested_loops_join(r1, key_idx1, r2, key_idx2)
        ro = nested_loops_join(Relation(tuple_header=header1, tuple_set=r1), Relation(header2, r2), keys).tuple_set
        sro = merge_sort_join(Relation(header1, r1), Relation(header2, r2), keys).tuple_set
        srow = merge_sort_join_wikipedia(Relation(header1, r1), Relation(header2, r2), keys).tuple_set
        hro = hash_join(Relation(header1, r1), Relation(header2, r2), keys).tuple_set
        shro = simple_hash_join(r1, key_idx1, r2, key_idx2)
        print(sorted(r1, key=lambda x: x[key_idx1]))
        print(sorted(r2, key=lambda x: x[key_idx2]))
        
        assert snro==ro, f"ouch! {set(ro).symmetric_difference(set(snro))}"
        assert snro==sro, f"ouch! {set(sro).symmetric_difference(set(snro))}"
        assert snro==srow, f"ouch! {set(srow).symmetric_difference(set(snro))}"
        assert snro==hro, f"ouch! {set(hro).symmetric_difference(set(snro))}"
        assert snro==shro, f"ouch! {set(hro).symmetric_difference(set(snro))}"
        
        print("ok")
    for rel1,rel2,keys in [(Relation(("X", "Y", "Z"), {(1,2,3),(1,3,4)}), Relation(("Y", "Z", "W"), {(2,3,99), (2,3,100)}), ("Y", "Z"))]:
        ro = nested_loops_join(rel1,rel2,keys).tuple_set
        sro = merge_sort_join(rel1,rel2,keys).tuple_set
        srow = merge_sort_join_wikipedia(rel1,rel2,keys).tuple_set
        hro = hash_join(rel1,rel2,keys).tuple_set
        print(sorted(rel1.tuple_set, key=partial(get_key_from_tuple, key_indices = [1,2])))
        print(sorted(rel2.tuple_set, key=partial(get_key_from_tuple, key_indices = [0,1])))
        
        assert ro==sro, f"ouch! {set(sro).symmetric_difference(set(ro))}"
        assert ro==srow, f"ouch! {set(srow).symmetric_difference(set(ro))}"
        assert ro==hro, f"ouch! {set(hro).symmetric_difference(set(ro))}"
        print(ro)
        print("ok")
    



def benchmark_join_algorithms():
    # It shoul show that hash and sort are similar with hash slightly faster, nested is much slower. Also simple versions are about 4x to 10x faster.
    key_idx1 = 1
    key_idx2 = 0
    keys = ("Z",)
    header1 = ("X", "Z")
    header2 = ("Z", "Y")
    for len1, len2, size in [(100,150,200),(1000,1500,200),(2000,3000,400),(4000,6000,500)]:
        print(len1, len2, size)
        r1 = {(random.randint(1,size),random.randint(1,size)) for x in range(len1)}
        r2 = {(random.randint(1,size),random.randint(1,size)) for x in range(len2)}
        print("len(r1): ", len(r1), "len1: ", len1) 
        print("len(r2): ", len(r2), "len2: ", len2) 
        # r1 = {(i,i) for i in range(len1)}
        # r2 = {(i+i%size,i+i%size) for i in range(len2)}
        snro = add_counter(simple_nested_loops_join)(r1, key_idx1, r2, key_idx2)
        ro = add_counter(nested_loops_join)(Relation(tuple_header=header1, tuple_set=r1), Relation(header2, r2), keys).tuple_set
        sro = add_counter(merge_sort_join)(Relation(header1, tuple_set=r1), Relation(header2, r2), keys).tuple_set
        srow = add_counter(merge_sort_join_wikipedia)(Relation(header1, r1), Relation(header2, r2), keys).tuple_set
        hro = add_counter(hash_join)(Relation(header1, r1), Relation(header2, r2), keys).tuple_set
        shro = add_counter(simple_hash_join)(r1, key_idx1, r2, key_idx2)
        # assert snro==ro, f"ouch! {set(ro).symmetric_difference(set(snro))}"
        # assert snro==sro, f"ouch! {set(sro).symmetric_difference(set(snro))}"
        # assert snro==srow, f"ouch! {set(srow).symmetric_difference(set(snro))}"
        # assert snro==hro, f"ouch! {set(hro).symmetric_difference(set(snro))}"
        # assert snro==shro, f"ouch! {set(hro).symmetric_difference(set(snro))}"
        print("ok, length of product relation is ", len(snro))

# check_join_algorithms()
# benchmark_join_algorithms()