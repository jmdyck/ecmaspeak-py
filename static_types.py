
# ecmaspeak-py/static_types.py:
# Code to handle static types for static type analysis.
#
# Copyright (C) 2023  J. Michael Dyck <jmdyck@ibiblio.org>

import re
from dataclasses import dataclass
from typing import Tuple, FrozenSet
from collections import defaultdict

import shared
from shared import stderr, spec
from Pseudocode_Parser import ANode
import records

# Before importing this module,
# you must ensure that a 'Spec' is loaded
# via shared.spec.restore().

_split_types_f = shared.open_for_output('split_types')

_subtype_memo = {}
_split_memo = {}

class Type():

    def set_of_types(self):
        return self.member_types if isinstance(self, UnionType) else frozenset([self])

    def __or__(A, B):
        if A == B: return A
        u = union_of_types([A, B])
        # print(A, '|', B, '=', u)
        return u

    def __lt__(A, B):
        return A.sort_key() < B.sort_key()

        # ... so that we can sort instances of classes derived from Type,
        # simply by having them define a `sort_key` method.
        #
        # There are only a couple places where we do such sorting:
        # - in the semantics for {NUM_COMPARISON},
        #   which generates multiple complaints due to STA's lack of smartness,
        #   and we want those complaints to be in a consistent order,
        #   to prevent spurious diffs.
        #   Eventually, STA may be smart enough that those complaints go away.
        # - in the semantics for {DOTTING},
        #   where again, we want error messages to appear in a consistent order.

    # -----------------------------------------------------

    # @memoize()
    def is_a_subtype_of_or_equal_to(A, B):

        if (A,B) in _subtype_memo:
            return _subtype_memo[(A,B)]
        # No speed-up?

        if B == T_Top_: return True

        A_members = A.set_of_types()
        B_members = B.set_of_types()

        if T_TBD in A_members or T_TBD in B_members:
            result = False

        elif A_members <= B_members:
            result = True

        # elif A_members > B_members:
        #     result = False
        # No, that assumes that A is 'reduced'.
        # But consider A = T_Normal | T_Reference_Record
        # and B = T_Normal

        else:
            # A is a subtype of B iff every A_member is a subtype of B.
            result = all(
                # and an A_member is a subtype of B
                # iff it is a subtype of some B_member
                any(
                    member_is_a_subtype_or_equal(A_member, B_member)
                    for B_member in B_members
                )
                for A_member in A_members
            )

        if 0:
            print(
                "SUBTYPING:",
                A,
                "is" if result else "is not",
                "a subtype of",
                B
            )

        _subtype_memo[(A,B)] = result

        return result

    # -----------------------------------------------------

    def split_by(A, B):
        # Return a pair of types that partition A
        # (i.e., two disjoint types whose union is A):
        # one that is a subtype of (or equal to) B,
        # and one that is outside of B.
        # (Either can be T_0.)

        # if A == T_TBD and B == ListType(T_String): pdb.set_trace()

        A_members = A.set_of_types()
        B_members = B.set_of_types()

        if (A,B) in _split_memo:
            return _split_memo[(A,B)]

        A_memtypes = A.set_of_types()
        B_memtypes = B.set_of_types()

        # A few cases that can be handled quickly:
        if A_memtypes == B_memtypes:
            inside_B  = A # or B
            outside_B = T_0

        # elif A_memtypes <= B_memtypes:
        #     inside_B  = A
        #     outside_B = T_0
        #
        # elif B_memtypes <= A_memtypes:
        #     inside_B  = B
        #     outside_B = union_of_types(A_memtypes - B_memtypes)
        #
        # e.g., if A == T_Completion_Record | T_throw_
        #      and B == T_Completion_Record
        # then the above will say
        #   inside_B == T_Completion_Record
        #  outside_B == T_throw_
        #
        # Now, you'd be right to point out that T_Completion_Record | T_throw_
        # shouldn't exist (it should just be T_Completion_Record).
        # TODO.

        else:
            # The general case:
            inside_B = set()
            outside_B = set()

            def recurse(A_subtypes, B_subtypes):
                for a in A_subtypes:
                    assert isinstance(a, Type)

                    # Treat T_TBD like Top
                    if a == T_TBD: a = T_Top_ # assert 0

                    if a == T_Normal and B == T_Completion_Record:
                        # A Completion Record is a Record, and Records are 'Normal' values,
                        # and so this would seem to be asking to split T_Normal
                        # into T_Completion_Record vs all the 'Normal' stypes other than T_Completion_Record.
                        # However, in practice, that's not what's wanted.
                        # Instead, we want to say that T_Normal and T_Completion_Record are completely disjoint.
                        outside_B.add(a)

                    elif a.is_a_subtype_of_or_equal_to(B):
                        inside_B.add(a)
                    else:
                        # get a list of the B_subtypes that are subtypes of a
                        bs_within_a = [
                            b
                            for b in B_subtypes
                            if b.is_a_subtype_of_or_equal_to(a)
                        ]
                        if bs_within_a:
                            # break down `a`
                            if a == T_List:
                                if len(bs_within_a) == 1:
                                    [bwa] = bs_within_a
                                    if isinstance(bwa, ListType):
                                        inside_B.add(bwa)
                                        outside_B.add(ListType(T_other_))
                                        # pdb.set_trace()
                                    else:
                                        assert 0
                                else:
                                    assert 0
                            elif isinstance(a, ListType):
                                if a == ListType(T_String | T_Undefined) and bs_within_a == [ListType(T_String)]:
                                    inside_B.add(ListType(T_String))
                                    outside_B.add(ListType(T_String | T_Undefined))
                                else:
                                    assert 0
                            elif isinstance(a, RecordType):
                                # TODO: be more general
                                ts_in_CR = [
                                    T_normal_completion,
                                    T_break_completion,
                                    T_continue_completion,
                                    T_return_completion,
                                    T_throw_completion
                                ]
                                if a == T_Completion_Record and set(bs_within_a) <= set(ts_in_CR):
                                    for t in ts_in_CR:
                                        if t in bs_within_a:
                                            inside_B.add(t)
                                        else:
                                            outside_B.add(t)
                                else:
                                    assert 0
                            else:
                                tnode = _tnode_for_type_[a]
                                a_imm_subtypes = [child.type for child in tnode.children]
                                recurse(a_imm_subtypes, bs_within_a)
                        else:
                            # no B_subtype is within `a`
                            # so `a` must be disjoint from B
                            outside_B.add(a)

            recurse(A_memtypes, B_memtypes)

            inside_B  = union_of_types(inside_B)
            outside_B = union_of_types(outside_B)

        print("%s :: %s  ===>  %s  ///  %s" %
            (A, B, outside_B, inside_B),
            file=_split_types_f)

        result = (inside_B, outside_B)
        _split_memo[(A,B)] = result
        return result


def member_is_a_subtype_or_equal(A, B):
    assert not isinstance(A, UnionType); assert A != T_TBD
    assert not isinstance(B, UnionType); assert B != T_TBD

    if A == B: return True

    if isinstance(A, HierType):
        if isinstance(B, HierType):
            A_tnode = _tnode_for_type_[A]
            B_tnode = _tnode_for_type_[B]
            if A_tnode.level < B_tnode.level:
                # A is higher in the hierarchy than B
                # (not necessarily an ancestor of B, but at a higher level).
                return False
            elif A_tnode.level == B_tnode.level:
                # They're at the same level in the hierarchy.
                # But we've already tested them for equality,
                # so they must be siblings/cousins.
                return False
            elif A_tnode.level > B_tnode.level:
                # A is at a lower level than B in the hierarchy.
                # So it might be a subtype.
                n_levels_diff = A_tnode.level - B_tnode.level
                tnode = A_tnode
                for i in range(n_levels_diff): tnode = tnode.parent
                assert tnode.level == B_tnode.level
                return (tnode is B_tnode)
            else:
                assert 0, "can't happen"
        else:
            # e.g., is Foo a subtype of List of Foo?
            # I don't think there's much need to say it is.
            return False

    elif isinstance(A, ListType):
        if isinstance(B, ListType):
            return (A.element_type.is_a_subtype_of_or_equal_to(B.element_type))
        elif isinstance(B, HierType):
            return (T_List.is_a_subtype_of_or_equal_to(B))
        elif isinstance(B, RecordType):
            return False
        else:
            assert 0, (A, B)

    elif isinstance(A, RecordType):
        if isinstance(B, RecordType):
            if A.schema_name == B.schema_name == '':
                A_field_dict = dict(A.fields_info)
                B_field_dict = dict(B.fields_info)
                if set(A_field_dict.keys()) == set(B_field_dict.keys()):
                    for (field_name, A_field_type) in A_field_dict.items():
                        B_field_type = B_field_dict[field_name]
                        if A_field_type.is_a_subtype_of_or_equal_to(B_field_type):
                            pass
                        else:
                            return False
                    return True
                else:
                    assert 0
            elif A.schema_name == '' and B.schema_name != '':
                return False
            elif A.schema_name != '' and B.schema_name == '':
                return False

            assert A.schema_name != ''
            assert B.schema_name != ''

            # TODO: normalize schema names
            A_record_schema = spec.RecordSchema_for_name_[A.schema_name]
            B_record_schema = spec.RecordSchema_for_name_[B.schema_name]

            for ars in A_record_schema.self_and_supers():
                if ars is B_record_schema:
                    # A_record_schema is the same as B_record_schema,
                    # or is a descendant schema of it.
                    break
            else:
                # A's schema isn't a descendant of B's
                return False

            # For any field that B constrains,
            # A must also constrain it, and constrain it the same or moreso.
            # (A can also have additional fields, that's fine.)

            # We assume that a RecordType never has a do-nothing field-constraint.
            # For example, consider a Reference Record's [[Strict]] field, declared to be a Boolean.
            # If A and B are both RecordTypes representing Reference Records,
            # and B.fields_info consists of a 'constraint' that [[Strict]] is Boolean
            # and A.fields_info is empty,
            # then they denote the same type,
            # but this code would incorrectly conclude that A isn't a subtype of or equal to B.
            for (B_field_name, B_field_type) in B.fields_info:
                # Linear search seems inefficient,
                # but in practice, the two fields_info are pretty short.
                for (A_field_name, A_field_type) in A.fields_info:
                    if A_field_name == B_field_name:
                        if A_field_type.is_a_subtype_of_or_equal_to(B_field_type):
                            # good so far
                            break
                        else:
                            return False
                else:
                    # Didn't break from the for-loop,
                    # i.e., didn't find a matching field_name in A.
                    # i.e., A.fields_info doesn't constrain {B_field_name},
                    # so A isn't a subtype of B.
                    # (Does this ever happen in practice?)
                    return False

            return True

        elif isinstance(B, HierType):
            if T_Record.is_a_subtype_of_or_equal_to(B):
                return True
            elif A.schema_name == 'Completion Record' and B == T_Completion_Record:
                return True
            else:
                return False
        elif isinstance(B, ListType):
            return False
        elif isinstance(B, ProcType):
            return False
        else:
            assert 0, (A, B)

    elif isinstance(A, ProcType):
        if isinstance(B, ProcType):
            assert len(A.param_types) == len(B.param_types)
            return (
                (
                    bpt.is_a_subtype_of_or_equal_to(apt) # contra-variance
                    for (apt, bpt) in zip(A.param_types, B.param_types)
                )
                and
                A.return_type.is_a_subtype_of_or_equal_to(B.return_type)
            )
        elif isinstance(B, HierType):
            return (T_proc_.is_a_subtype_of_or_equal_to(B))
        elif isinstance(B, ListType):
            return False
        elif isinstance(B, RecordType):
            return False
        else:
            assert 0, (A, B)

    else:
        assert 0, (A, B)


    # --------------------------------------------------------------------------

@dataclass(frozen = True)
class TBDType(Type):
    pass

    def __str__(self): return 'TBD'
    def unparse(self, parenthesuze=False): return 'TBD'

@dataclass(frozen = True)
class HierType(Type):
    name: str

    # The instances of this class represent static types that form a hierarchy.
    # Specifically, for any two such types A and B,
    # it must be the case that either:
    #  - A == B,
    #  - A is a subtype of B,
    #  - B is a subtype of A, or
    #  - A and B are disjoint.
    #
    # (Note that this condition *doesn't* hold for
    # UnionTypes, ProcTypes, etc.)

    def __post_init__(self):
        assert isinstance(self.name, str)
        assert re.fullmatch(r'[\w -]+', self.name), self.name
        assert not self.name.startswith('a '), self.name

    def sort_key(self):
        return ('HierType', self.name)

    def __str__(self):
        if self.name.endswith('_completion'):
            return self.name.removesuffix('completion')
        return self.name

    def unparse(self, parenthesize=False):
        if self.name.startswith('PTN_'):
            x = 'Parse Node for |%s|' % self.name.replace('PTN_','')
            if parenthesize: x = '(%s)' % x
            return x
        else:
            return self.__str__()

@dataclass(frozen = True)
class ListType(Type):
    element_type: Type

    def __post_init__(self):
        assert isinstance(self.element_type, Type)

    def sort_key(self):
        return ('ListType', self.element_type)

    def __str__(self): return "List of %s" % str(self.element_type)
    def unparse(self, _=False): return "List of %s" % self.element_type.unparse(True)

@dataclass(frozen = True)
class RecordType(Type):
    schema_name: str
    fields_info: Tuple[Tuple[str, Type]]

    def __post_init__(self):
        assert isinstance(self.schema_name, str)
        assert isinstance(self.fields_info, tuple)
        for fi in self.fields_info:
            assert isinstance(fi, tuple)
            (field_name, field_type) = fi
            assert isinstance(field_name, str)
            assert isinstance(field_type, Type)

    def sort_key(self):
        return ('RecordType', self.schema_name, self.fields_info)

    def type_of_field_named(self, field_name):
        for (f_name, f_type) in self.fields_info:
            if f_name == field_name:
                return f_type

        # To get here, we didn't 'return' above, which means that
        # {field_name} didn't appear in {self.fields_info}
        # which you might think means that (the type represented by) {self}
        # only includes records that don't have a field by that name.
        # On the contrary, it *does* include records with such a field,
        # it just doesn't constrain the type of such a field
        # (any more than {self}'s super-schemas might).

        if self.schema_name == 'Completion Record':
            # For some of the fields,
            # the 'declared' types aren't as precise as they could be.

            if field_name == '[[Type]]':
                # In practice, this would have been handled by the for-loop above.
                # But I suppose it could happen.
                return T_tilde_break_ | T_tilde_continue_ | T_tilde_normal_ | T_tilde_return_ | T_tilde_throw_

            else:
                assert field_name in ['[[Value]]', '[[Target]]']
                if self.fields_info == ():
                    # {self} is just T_Completion_Record,
                    # so the types of its fields are the most general
                    return {
                        '[[Value]]' : T_Normal,
                        '[[Target]]': T_String | T_tilde_empty_,
                    }[field_name]
                else:
                    (Type_field_name, Type_field_stype) = self.fields_info[0]
                    assert Type_field_name == '[[Type]]'
                    assert isinstance(Type_field_stype, HierType)
                    if Type_field_stype == T_tilde_normal_:
                        return {
                            '[[Value]]' : T_Normal,
                            '[[Target]]': T_tilde_empty_,
                        }[field_name]

                    elif Type_field_stype in [T_tilde_return_, T_tilde_throw_]:
                        return {
                            '[[Value]]' : T_Tangible_ | T_tilde_empty_,
                            '[[Target]]': T_tilde_empty_,
                        }[field_name]

                    elif Type_field_stype in [T_tilde_break_, T_tilde_continue_]:
                        return {
                            '[[Value]]' : T_Tangible_ | T_tilde_empty_,
                            '[[Target]]': T_String | T_tilde_empty_,
                        }[field_name]

                    else:
                        assert 0

        # ---------------------------
        assert 0

        # code that we might need in future:
        record_schema = spec.RecordSchema_for_name_[self.schema_name]
        for ars in record_schema.self_and_supers():
            if field_name in ars.addl_field_decls:
                field_decl = ars.addl_field_decls[field_name]
                field_decl.value_description

        return T_Normal

    def __str__(self):

        if self == T_Completion_Record: return 'Completion Record'

        if self.schema_name == 'Completion Record' and len(self.fields_info) in [1,2]:
            fields_d = dict(self.fields_info)
            Type_field_stype = fields_d['[[Type]]']
            prefix = Type_field_stype.name.replace('tilde_', '')

            if len(self.fields_info) == 1:
                suffix = ''
            else:
                Value_field_stype = fields_d['[[Value]]']
                suffix = f"({Value_field_stype})"

            return f"{prefix}{suffix}"

        field_types_str = ', '.join(
            f"{f_name}: {f_type}"
            for (f_name, f_type) in self.fields_info
        )
        return f"RecordType({self.schema_name!r}, {field_types_str})"

    def unparse(self, _=False):
        return str(self)

def s_dot_field(lhs_type, field_name):
    if isinstance(lhs_type, RecordType):
        return lhs_type.type_of_field_named(field_name)
    elif isinstance(lhs_type, UnionType):
        field_types = []
        for memtype in lhs_type.set_of_types():
            assert isinstance(memtype, RecordType)
            field_types.append(memtype.type_of_field_named(field_name))
        return union_of_types(field_types)
    else:
        assert 0

@dataclass(frozen = True)
class ProcType(Type):
    param_types: Tuple[Type]
    return_type: Type

    def __post_init__(self):
        assert isinstance(self.param_types, tuple)
        for pt in self.param_types: assert isinstance(pt, Type)
        assert isinstance(self.return_type, Type)

    def sort_key(self):
        return ('ProcType', self.param_types, self.return_type)

    def __str__(self):
        if self == T_MatcherContinuation:
            return "MatcherContinuation"
        elif self == T_Matcher:
            return "Matcher"
        elif self == T_ReadModifyWrite_modification_closure:
            return "ReadModifyWrite_modification_closure"
        elif self == T_RegExpMatcher_:
            return "RegExpMatcher_"
        else:
            return "{(%s) -> %s}" % (
                ', '.join(str(pt) for pt in self.param_types),
                self.return_type
            )
    def unparse(self, _=False): return str(self)

@dataclass(frozen = True)
class UnionType(Type):
    # A union of (non-union) types.
    # Must satisfy the constraint that no member-type
    # is a subtype or supertype of any other member-type.
    # (XXX: Should check that in __new__.)

    member_types: FrozenSet[Type]

    def __post_init__(self):
        assert len(self.member_types) != 1
        for mt in self.member_types:
            assert isinstance(mt, Type)
            assert not isinstance(mt, UnionType)

    def sort_key(self):
        return ('UnionType', self.member_types)

    def __str__(self): return "(%s)" % ' | '.join(sorted(map(str, self.member_types)))

    def unparse(self, parenthesize=False):
        if T_not_passed in self.member_types:
            # This only makes sense for a top-level type,
            # but I don't think it'll occur anywhere else.
            prefix = '(optional) '
            member_types = set(self.member_types)
            member_types.remove(T_not_passed)
        else:
            prefix = ''
            member_types = self.member_types

        if self == T_abrupt_completion: return 'Abrupt'

        x = ' | '.join(sorted(
            member_type.unparse()
            for member_type in member_types
        ))
        if parenthesize: x = '(' + x + ')'
        return prefix + x

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

# memoize
def union_of_types(types):
    if len(types) == 0: return T_0

    types1 = set(types)

    if len(types1) == 1: return types1.pop()

    types1.discard(T_0)

    if len(types1) == 1: return types1.pop()

    types1.discard(T_TBD)

    if len(types1) == 1: return types1.pop()

    # ----------------------------

    memtypes = set()
    for t in types1:
        if isinstance(t, UnionType):
            for mt in t.member_types:
                assert not isinstance(mt, UnionType)
                memtypes.add(mt)
        else:
            memtypes.add(t)

    memtypes.discard(T_TBD)
    assert len(memtypes) > 0

    list_memtypes = []
    record_memtypes = []
    proc_memtypes = []
    hier_memtypes = []
    for mt in memtypes:
        if mt == T_List or isinstance(mt, ListType):
            list_memtypes.append(mt)
        elif isinstance(mt, RecordType):
            record_memtypes.append(mt)
        elif isinstance(mt, ProcType):
            # There isn't a T_Proc, or a HierType that resolves to a ProcType.
            proc_memtypes.append(mt)
        elif isinstance(mt, HierType):
            hier_memtypes.append(mt)
        else:
            assert 0, mt

    result_memtypes = (
        _union_of_list_memtypes(list_memtypes)
        + _union_of_record_memtypes(record_memtypes)
        + _union_of_proc_memtypes(proc_memtypes)
        + _union_of_hier_memtypes(hier_memtypes)
    )

    assert result_memtypes

    if len(result_memtypes) == 1:
        result = list(result_memtypes)[0]
    else:
        result = UnionType(frozenset(result_memtypes))

    # print("union of", ', '.join(str(t) for t in types), " = ", result)

    return result

# ------------------------------------------------------------------------------

def _union_of_list_memtypes(list_memtypes):

    if len(list_memtypes) <= 1:
        return list_memtypes

    if T_List in list_memtypes:
        # For the purposes of type-union,
        # T_List is basically "List of TBD",
        # and because len(list_memtypes) >= 2,
        # there must be a more specfic list-type in the set,
        # so ignore T_List.
        list_memtypes.remove(T_List)

    if len(list_memtypes) == 1:
        return list_memtypes

    t = ListType(
        union_of_types([
            mt.element_type
            for mt in list_memtypes
        ])
    )

    return [t]

# ------------------------------------------------------------------------------

def _union_of_record_memtypes(record_memtypes):

    if len(record_memtypes) <= 1:
        return record_memtypes

    memtypes_with_schema_name_ = defaultdict(list)
    for memtype in record_memtypes:
        assert isinstance(memtype, RecordType)
        memtypes_with_schema_name_[memtype.schema_name].append(memtype)

    result_memtypes = []

    for (schema_name, memtypes) in memtypes_with_schema_name_.items():
        assert len(memtypes) > 0
        if len(memtypes) == 1:
            result_memtypes.extend(memtypes)
        else:
            if schema_name == '':
                result_memtypes.extend(memtypes)
                #XXX for now
            elif schema_name == 'Completion Record':
                crtypes_with_Type_stype_ = defaultdict(list)
                for crtype in memtypes:
                    if crtype.fields_info == ():
                        # {crtype} is a supertype (or equal to) all others in {memtypes}
                        result_memtypes.append(crtype)
                        break
                    else:
                        (Type_field_name, Type_field_stype) = crtype.fields_info[0]
                        assert Type_field_name == '[[Type]]'
                        if isinstance(Type_field_stype, HierType):
                            crtypes_with_Type_stype_[Type_field_stype].append(crtype)
                        elif isinstance(Type_field_stype, UnionType):
                            for sub_tfs in Type_field_stype.member_types:
                                assert isinstance(sub_tfs, HierType)
                                sub_crtype = RecordType(
                                    crtype.schema_name,
                                    (('[[Type]]', sub_tfs),)
                                    +
                                    crtype.fields_info[1:]
                                )
                                crtypes_with_Type_stype_[sub_tfs].append(sub_crtype)
                        else:
                            assert 0
                else:
                    # no break from above loop,
                    # i.e. no crtype with this schema_name had an empty fields_info
                    # i.e. each crtype with this schema_name has a [[Type]] field
                    # So we consider them separately depending on the value (stype) of the [[Type]] field.
                    for (Type_field_stype, crtypes) in crtypes_with_Type_stype_.items():
                        if len(crtypes) == 1:
                            result_memtypes.extend(crtypes)
                        else:
                            # Okay, so we have multiple crtypes,
                            # all with the same schema_name and the same value for [[Type]] field.
                            # But they might or might not have a [[Value]] field.
                            # (e.g., T_throw_completion(TypeError) vs T_throw_completion)
                            Value_field_stypes = []
                            for crtype in crtypes:
                                assert len(crtype.fields_info) >= 1
                                if len(crtype.fields_info) == 1:
                                    # {crtype} is a supertype (or equal to) all others in {crtypes}
                                    result_memtypes.append(crtype)
                                    break
                                else:
                                    (Value_field_name, Value_field_stype) = crtype.fields_info[1]
                                    assert Value_field_name == '[[Value]]'
                                    Value_field_stypes.append(Value_field_stype)
                            else:
                                # no break from above loop,
                                # i.e. no crtype in {crtypes} had just a [[Type]] field
                                # i.e. each crtype in {crtypes} has both [[Type]] and [[Value]] field
                                result_memtypes.append(
                                    RecordType(schema_name, (
                                            ('[[Type]]', Type_field_stype),
                                            ('[[Value]]', union_of_types(Value_field_stypes)),
                                        )
                                    )
                                )
            else:
                assert 0, schema_name

    return result_memtypes

# ------------------------------------------------------------------------------

def _union_of_proc_memtypes(proc_memtypes):

    if len(proc_memtypes) <= 1:
        return proc_memtypes

    assert 0

# ------------------------------------------------------------------------------

def _union_of_hier_memtypes(memtypes):

    for memtype in memtypes:
        assert isinstance(memtype, HierType)

    if len(memtypes) <= 1:
        return memtypes

    memtypes_set = set(memtypes)

    def recurse(tnode):
        if not tnode.children: return

        if tnode.type in memtypes_set:
            # {tnode.type} subsumes all subtypes,
            # so since {tnode.type} is in {memtypes_set}
            # remove any of its subtypes that are in {memtypes_set}.
            rm_all_descendants_of(tnode)

        else:
            # {tnode.type} isn't in memtypes_set,
            # but if all of its children are,
            # then we can replace them with {tnode.type}

            for child_tnode in tnode.children:
                recurse(child_tnode)

            if all(
                child_tnode.type in memtypes_set
                for child_tnode in tnode.children
            ):
                stderr("! replacing ...")
                for child_tnode in tnode.children:
                    stderr("!    ", child_tnode.type)
                    memtypes_set.remove(child_tnode.type)
                stderr("! with", tnode.type)
                memtypes_set.add(tnode.type)

    def rm_all_descendants_of(tnode):
        for child_tnode in tnode.children:
            memtypes_set.discard(child_tnode.type)
            rm_all_descendants_of(child_tnode)

    recurse(troot)

    return list(memtypes_set)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# instances of HierType

_named_type_hierarchy = {
    'Top_': {
        'Absent': {
            'not_passed': {},    # for an optional parameter
            'not_in_node': {},   # for an optional child of a node
            'not_set': {},       # for a metavariable that might not be initialized
            'not_returned': {},  # for when control falls off the end of an operation
        },
        'Normal': {
            'Tangible_': {
                'Primitive': {
                    'Undefined': {},
                    'Null': {},
                    'Boolean': {},
                    'String': {},
                    'Symbol': {},
                    'Number': {
                        'FiniteNumber_' : {
                            'IntegralNumber_': {},
                            'NonIntegralFiniteNumber_' : {}
                        },
                        'NegInfinityNumber_': {},
                        'PosInfinityNumber_': {},
                        'NaN_Number_': {},
                    },
                    'BigInt': {},
                },
                'Object': {
                    'Error': {
                        'AggregateError': {},
                        'ReferenceError': {},
                        'SyntaxError': {},
                        'TypeError': {},
                        'RangeError': {},
                        'other_Error_': {},
                    },
                    # 'Proxy': {},
                    # 'RegExp': {},
                    'ArrayBuffer_object_': {},
                    'Array_object_': {},
                    'AsyncGenerator_object_': {},
                    'FinalizationRegistry_object_': {},
                    'Generator_object_': {},
                    'Iterator_object_': {},
                    'IteratorResult_object_': {},
                    'Promise_object_': {},
                    'SharedArrayBuffer_object_': {},
                    'String_exotic_object_': {},
                    'TypedArray_object_': {},
                    'WeakMap_object_': {},
                    'WeakRef_object_': {},
                    'WeakSet_object_': {},
                    'function_object_': {
                        'ECMAScript_function_object_': {},

                        'built_in_function_object_': {},
                        # The spec allows a built-in function to be implemented
                        # as an ECMAScript function object or not.
                        # I.e., you can have an object that is *both*
                        # an ECMAScript function object and a built-in function object.
                        #
                        # However, the spec never focuses on such an object,
                        # or on an ES function that isn't a built-in function,
                        # or on a built-in function that isn't an ES function.
                        #
                        # So for the purposes of static analysis,
                        # it works to treat them as mutually exclusive.
                        #
                        # (There's editorial desire to eliminate that choice,
                        # or at least, eliminate the spec's mentioning/stressing that choice,
                        # at which point I can probably delete this comment.

                        'constructor_object_': {}, # XXX This is actually orthogonal to ECMAScript/built-in/Proxy/Bound/other
                        'Proxy_exotic_object_': {},
                        'bound_function_exotic_object_': {},
                        'other_function_object_': {},
                    },
                    'other_Object_': {},
                },
            },
            'Intangible_': {
                'CaptureRange': {},
                'CharSet': {},
                'CharSetElement': {},
                'Data Block': {},
                'event_pair_': {},
                'IEEE_binary32_': {},
                'IEEE_binary64_': {},
                'LangTypeName_': {},
                'List': {},
                'MatchResult': {
                    'MatchState': {},
                    'tilde_failure_': {},
                },
                'ExtendedMathReal_': {
                    'MathReal_': {
                        'MathInteger_': {
                            'code_unit_' : {},
                            'code_point_': {},
                            'MathIntegerOther_' : {},
                        },
                        'MathOther_': {},
                    },
                    'MathPosInfinity_': {},
                    'MathNegInfinity_': {},
                },
                'Parse Node' : {
                    'PTN_ForBinding': {},
                    'PTN_Script': {},
                    'PTN_Pattern': {},
                    'PTN_Template_Literal': {},
                },
                'Private Name': {},
                'Record': {
                    'Intrinsics Record': {},
                },
                # 'Reference': {}, # 2085
                'Relation': {},
                'Set': {},
                'Shared Data Block': {},
                    # The name suggests a subtype of Data Block,
                    # but doesn't seem to be treated that way.
                'SlotName_': {},
                'TypedArray_element_type': {
                    # children are filled in via code
                },
                'agent_signifier_' : {},
                'alg_steps': {},
                # 'character_': {
                #     # 'code_unit_': {},
                #     'code_point_': {},
                # },
                'completion_kind_': {},
                'execution context': {},
                'grammar_symbol_': {},
                'host_defined_': {},
                'proc_': {},
                'property_': {
                    'data_property_': {},
                    'accessor_property_': {},
                },
                'tilde_': {
                    # children are filled in via code
                },
                'other_': {},
            },
        },
    }
}

_tnode_for_type_ = {}

class TNode:
    def __init__(self, type, parent):
        assert isinstance(type, Type)
        assert parent is None or isinstance(parent, TNode)
        self.type = type
        self.parent = parent

        self.children = []

        if parent is None:
            self.level = 0
        else:
            self.level = parent.level + 1
            parent.children.append(self)

        _tnode_for_type_[type] = self

def _HierType_etc(type_name):
    assert isinstance(type_name, str)
    t = HierType(type_name)
    variable_name = 'T_' + type_name.replace(' ', '_').replace('-', '_')
    globals()[variable_name] = t
    return t

def _traverse(typesdict, p):
    for (type_name, subtypesdict) in typesdict.items():
    # sorted(typesdict.items(), key=lambda tup: 1 if tup[0] == 'List' else 0):
        type = _HierType_etc(type_name)
        tnode = TNode(type, p)
        _traverse(subtypesdict, tnode)

stderr("initializing the type hierarchy...")
_traverse(_named_type_hierarchy, None)

troot = _tnode_for_type_[T_Top_]

# ------------------------------------------------------------------------------
# Parse Node types

def ptn_type_for(nonterminal):
    if isinstance(nonterminal, str):
        if nonterminal.startswith('|'):
            assert nonterminal.endswith('|')
            nont_basename = nonterminal[1:-1]
        else:
            nont_basename = nonterminal
        optionality = ''
    elif isinstance(nonterminal, ANode):
        assert nonterminal.prod.lhs_s == '{nonterminal}'
        [nonterminal_ref] = nonterminal.children
        mo = re.fullmatch(r'\|(\w+)((?:\[[^][]+\])?)(\??)\|', nonterminal_ref)
        assert mo
        [nont_basename, params, optionality] = mo.groups()
    else:
        assert 0
    type_name = 'PTN_' + nont_basename
    type = HierType(type_name)
    if optionality: type = type | T_not_in_node
    return type

def _make_parse_node_types():
    # Find all the Nonterminals, and create a HierType and a TNode for each.
    nonterminals = set()
    for grammar in spec.grammar_.values():
        for lhs in grammar.prodn_for_lhs_.keys():
            nonterminals.add(lhs)

    for nonterminal_name in sorted(list(nonterminals)):
        t = ptn_type_for(nonterminal_name)
        if t not in _tnode_for_type_:
            parent_type = T_Parse_Node
            TNode(t, _tnode_for_type_[parent_type])
            # which has the side-effect of adding it to _tnode_for_type_

_make_parse_node_types()

# ------------------------------------------------------------------------------

# Define tilde-types

# The spec doesn't have a form for 'declaring' tilde-words,
# so all you can do is look for uses of them.
# There are various places that tilde-words appear,
# but it turns out you can find all the distinct ones
# by looking for them just in algorithms.

def _define_tilde_types():
    tilde_words = set()
    for bif_or_op in ['bif', 'op']:
        for alg in spec.alg_info_[bif_or_op].values():
            for alg_defn in alg.all_definitions():
                st = alg_defn.anode.source_text()
                for tilde_word in re.findall(r'~\S+~', st):
                    tilde_words.add(tilde_word)

    for tilde_word in sorted(tilde_words):
        if tilde_word == '~failure~':
            parent_type = T_MatchResult
            continue # For now, it's clearer if it appears in the _named_type_hierarchy
        elif re.fullmatch(r'~\w+(8|8C|16|32|64)~', tilde_word):
            parent_type = T_TypedArray_element_type
        else:
            parent_type = T_tilde_
        parent_tnode = _tnode_for_type_[parent_type]

        tilde_type_name = 'tilde' + re.sub('\W', '_', tilde_word)
        type = _HierType_etc(tilde_type_name)
        tnode = TNode(type, parent_tnode)

_define_tilde_types()

# ------------------------------------------

def type_for_ERROR_TYPE(error_type):
    st = error_type.source_text()
    assert st.startswith('*')
    assert st.endswith('*')
    error_type_name = st[1:-1]
    return HierType(error_type_name)

def type_for_TYPE_NAME(type_name):
    assert isinstance(type_name, ANode)
    assert type_name.prod.lhs_s == '{TYPE_NAME}'
    st = type_name.source_text()
    return HierType(st)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# instances of RecordType

# The spec declares Module Record with only one sub-schema, Cyclic Module Record.
# And it declares Cyclic Module Record with only one sub-schema, Source Text Module Record.
# But letting that stand causes problems for STA,
# because it assumes you can replace a union-of-all-subtypes with the supertype,
# but we don't want to replace (e.g.) Cyclic Module Record with Module Record.
# The spec assumes that other specs/implementations can define
# other sub-schemas of [Cyclic] Module Record,
# so we create some ad hoc sub-schemas to prevent the union-of-all-subtypes mistake.
_rs = records.RecordSchema('other Module Record', 'Module Record')
_rs = records.RecordSchema('other Cyclic Module Record', 'Cyclic Module Record')

def _traverse_record_schema(super_schema, super_tnode):
    for sub_schema in super_schema.sub_schemas:
        if sub_schema.tc_schema_name == 'Completion Record':
            # Don't create HierType('Completion Record'),
            # because that would complicate things.
            # Instead, we create T_Completion_Record as a RecordType.
            continue
        sub_type = _HierType_etc(sub_schema.tc_schema_name)
        sub_tnode = TNode(sub_type, super_tnode)
        _traverse_record_schema(sub_schema, sub_tnode)

_traverse_record_schema(spec.root_RecordSchema, _tnode_for_type_[T_Record])

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# Misc specific types that are referenced above,
# and so have to be declared within this module.

T_0 = UnionType(frozenset())

T_TBD = TBDType()

# ------------------------------------------------------------------------------
#@ 6.2.4 The Completion Record Specification Type

T_Completion_Record = RecordType('Completion Record', ())
# We create this rather than creating HierType('Completion Record')
# in _traverse_record_schema.

def CompletionType(Type_field_stype):
    return RecordType('Completion Record', (('[[Type]]', Type_field_stype),))

T_normal_completion   = CompletionType(T_tilde_normal_)
T_break_completion    = CompletionType(T_tilde_break_)
T_continue_completion = CompletionType(T_tilde_continue_)
T_return_completion   = CompletionType(T_tilde_return_)
T_throw_completion    = CompletionType(T_tilde_throw_)

T_abrupt_completion = T_continue_completion | T_break_completion | T_return_completion | T_throw_completion

# ------------------------------------------------------------------------------
# Proc types, only because we special-case ProcType.__str__ for them

T_Job = ProcType((), T_Tangible_ | T_tilde_empty_ | T_throw_completion)

T_MatcherContinuation = ProcType((T_MatchState,                      ), T_MatchResult)
T_Matcher             = ProcType((T_MatchState, T_MatcherContinuation), T_MatchResult)

T_character_ = T_code_unit_ | T_code_point_
T_MathNonNegativeInteger_ = T_MathInteger_ # for now
T_RegExpMatcher_      = ProcType((ListType(T_character_), T_MathNonNegativeInteger_), T_MatchResult)

T_ReadModifyWrite_modification_closure = ProcType((ListType(T_MathInteger_), ListType(T_MathInteger_)), ListType(T_MathInteger_))

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

# vim: sw=4 ts=4 expandtab
