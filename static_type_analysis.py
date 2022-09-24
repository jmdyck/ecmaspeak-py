#!/usr/bin/python3

# ecmaspeak-py/static_type_analysis.py:
# Perform static type analysis/inference on the spec's pseudocode.
#
# Copyright (C) 2018  J. Michael Dyck <jmdyck@ibiblio.org>

import re, atexit, time, sys, pdb
from operator import itemgetter
from collections import OrderedDict, defaultdict
from itertools import zip_longest
from pprint import pprint

import shared, HTML
from shared import stderr, spec, DL
from Pseudocode_Parser import ANode
from Graph import Graph

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def main():
    outdir = sys.argv[1]

    shared.register_output_dir(outdir)
    spec.restore()

    prep_for_STA()
    gather_nonterminals()
    levels = compute_dependency_levels()
    do_static_type_analysis(levels)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def prep_for_STA():
    stderr('prep_for_STA ...')

    global un_f
    un_f = shared.open_for_output('unconverted_natures')

    shared.prep_for_line_info()

    for bif_or_op in ['bif', 'op']:
        for alg in spec.alg_info_[bif_or_op].values():
            for header in alg.headers:
                header.tah = TypedAlgHeader(header)

    un_f.close()
    print_unused_type_tweaks()

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def gather_nonterminals():
    # Find all the Nonterminals that are mentioned in pseudocode,
    # and create a NamedType and a TNode for each.
    #
    # This is a kludge because grammar info doesn't get passed through pickling yet.

    global nonterminals
    nonterminals = set()

    stderr("gather_nonterminals...")

    def recurse_h(hnode):
        if hasattr(hnode, '_syntax_tree'):
            if hnode._syntax_tree is not None:
                recurse_a(hnode._syntax_tree)

        else:
            for child in hnode.children:
                recurse_h(child)

    def recurse_a(anode):
        if isinstance(anode, str): return
        assert isinstance(anode, ANode)
#        if anode.prod.lhs_s == '{CONDITION_1}':
#            print(anode.source_text())
        if anode.prod.lhs_s == '{nonterminal}':
            [nonterminal_name] = anode.children
            if '[' in nonterminal_name or '?' in nonterminal_name:
                return
            nonterminals.add(nonterminal_name)
        else:
            for child in anode.children:
                recurse_a(child)

    recurse_h(spec.doc_node)
#    sys.exit(1)

    for nonterminal_name in sorted(list(nonterminals)):
        # print(nonterminal_name)
        t = ptn_type_for(nonterminal_name)
        if t not in tnode_for_type_:
            parent_type = T_Parse_Node
            TNode(t, tnode_for_type_[parent_type])
            # which has the side-effect of adding it to tnode_for_type_

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

# Handle built-in operations?
built_in_ops = [
    # true built-ins:
    'abs',
    'floor',
    'min',

    # defined as shorthands:
    'Completion',
    # 'IfAbruptRejectPromise',

    # not built-in at all,
    # but defined by <emu-eqn>,
    # which I don't want to deal with just yet:
    'DateFromTime',
    'MonthFromTime',
    'YearFromTime',
    'WeekDay',
]

def compute_dependency_levels():
    stderr()
    stderr('analyzing dependencies...')

    alg_items = sorted(spec.alg_info_['bif'].items()) + sorted(spec.alg_info_['op'].items())

    for (_, alg) in alg_items:
        summarize_headers(alg)

    # Analyze the definition(s) of each named operation to find its dependencies.
    dep_graph = Graph()
    for (_, alg) in alg_items:
        dep_graph.add_vertex(alg)

        for callee in sorted(alg.callees):
            if alg.name in ['ToNumber', 'ToString'] and callee in ['ToPrimitive']: continue # XXX for now
            if callee not in spec.alg_info_['op']:
                print("unknown operation:", callee)
            else:
                callee_alg = spec.alg_info_['op'][callee]
                dep_graph.add_arc(alg, callee_alg)

    f = shared.open_for_output('deps')
    dep_graph.print_arcs(file=f)

    # Based on all that dependency info, compute the dep levels.
    levels = dep_graph.compute_dependency_levels()

    # Print levels
    for (L, clusters_on_level_L) in enumerate(levels):
        print(file=f)
        print("level %d (%d clusters):" % (L, len(clusters_on_level_L)), file=f)
        for cluster in clusters_on_level_L:
            print("    cluster #___ (%d members, %d direct prerequisite clusters):" % (
                # cluster.number,
                len(cluster.members), len(cluster.direct_prereqs)),
                file=f
            )
            for vertex in cluster.members:
                print("       ", vertex, file=f)

    f.close()
    # sys.exit(0)
    return levels

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def summarize_headers(alg):
    if len(alg.headers) == 0:
        print("no headers for", alg.species, alg.name)
    elif len(alg.headers) == 1:
        [header] = alg.headers
        alg.parameters_with_types = header.tah.parameter_types.items()
        alg.return_type = header.tah.return_type

    else:
        assert alg.species.startswith('op: discriminated'), alg.species
        n_params = len(alg.headers[0].tah.parameter_types)
        assert all(len(header.tah.parameter_types) == n_params for header in alg.headers)

        param_names_ = [set() for i in range(n_params)]
        param_types_ = [set() for i in range(n_params)]
        return_types = set()
        for header in alg.headers:
            for (i, (param_name, param_type)) in enumerate(header.tah.parameter_types.items()):
                param_names_[i].add(param_name)
                param_types_[i].add(param_type)
            return_types.add(header.tah.return_type)

        alg.parameters_with_types = [
            (
                '|'.join(sorted(list(param_names_[i])))
            ,
                union_of_types(param_types_[i])
            )
            for i in range(n_params)
        ]
        alg.return_type = union_of_types(return_types)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

class TypedAlgHeader:

    def __init__(self, header):

        self.species = header.species
        self.name = header.name
        self.name_w_markup = header.name_w_markup
        self.param_names = header.param_names()
        self.description = header.description

        # ----

        self.initial_parameter_types = OrderedDict()

        for param in header.params:
            if param.decl_node:
                (_, _, param_nature_node) = param.decl_node.children
                pt = convert_nature_node_to_type(param_nature_node)
            else:
                pt = convert_nature_to_type(param.nature)

            if param.punct == '[]':
                pt = pt | T_not_passed

            self.initial_parameter_types[param.name] = pt

        self.parameter_types = self.initial_parameter_types.copy()

        # ----

        self.initial_return_type = convert_nature_node_to_type(header.return_nature_node)

        self.return_type = self.initial_return_type

        # ----

        self.for_phrase = header.for_phrase
        if self.for_phrase is None:
            self.for_param_type = None
            self.for_param_name = None
        else:
            mo = re.fullmatch(r'(.+) (_\w+_)(?: \(.+\))?', self.for_phrase)
            if mo:
                (for_param_nature, self.for_param_name) = mo.groups()
            else:
                for_param_nature = self.for_phrase
                self.for_param_name = None
            self.for_param_type = convert_nature_to_type(for_param_nature)

        self.fake_node_for_ = {}
        for pname in self.param_names:
            self.fake_node_for_[pname] = ANode(None, None, 0, 0)
        self.fake_node_for_['normal'] = ANode(None, None, 0, 0)
        self.fake_node_for_['abrupt'] = ANode(None, None, 0, 0)
        self.fake_node_for_['*return*'] = ANode(None, None, 0, 0)

        # -------------------------

        # tweak some parameter/return types:
        # Theoretically, the STA would figure all this out,
        # but (a) it's not that smart, and (b) this saves some churn.
        if self.name in type_tweaks_for_op_:
            tweaks = type_tweaks_for_op_[self.name]
            for (ton, tpn, tot, tnt) in tweaks.tweaks:
                # NUMBER=INTEGER?
                if tot == T_Number and tnt == T_Number: continue
                try:
                    old_type = self.return_type if tpn == '*return*' else self.parameter_types[tpn]
                except KeyError:
                    print("type_tweaks: %s does not have param named %s" % (ton, tpn))
                    sys.exit(1)
                if tot != old_type:
                    # This can happen ...
                    # because return-type is split in spec,
                    # and fake_node only points to the abrupt part.
                    # "warning: tweak %s fails old-type check: In %s, existing type of %s is %s, not %s" % (
                    # (ton, tpn, tot, tnt), self.name, tpn, old_type, tot)
                    stderr()
                    stderr('tweak:')
                    stderr('  op_name  :', ton)
                    stderr('  param    :', tpn)
                    stderr('  old_type :', tot)
                    stderr('  new_type :', tnt)
                    stderr('stated type:', old_type)
                    sys.exit(1)
                self.change_declared_type(tpn, tnt, tweak=True)
            tweaks.n_uses += 1

        elif self.name == 'Evaluation':
            # too weird to handle above
            tpn = '*return*'
            assert self.return_type in [(T_Normal | T_Abrupt), T_TBD]
            tnt = T_Tangible_ | T_empty_ | T_Reference_Record | T_Abrupt
            self.change_declared_type(tpn, tnt, tweak=True)

        # -------------------------

        self.t_defns = []

        for alg_defn in header.u_defns:
            if self.species.startswith('op: discriminated by syntax'):
                discriminator = alg_defn.discriminator
            elif self.for_param_type:
                discriminator = self.for_param_type
            elif alg_defn.discriminator:
                discriminator = NamedType(alg_defn.discriminator)
            else:
                discriminator = None

            if self.species.startswith('op: discriminated by syntax'):
                assert (
                    discriminator is None
                    or
                    isinstance(discriminator, HTML.HNode)
                        and discriminator.element_name in ['emu-grammar', 'p']
                    or
                    isinstance(discriminator, ANode)
                        and discriminator.prod.lhs_s in ['{h_emu_grammar}', '{nonterminal}']
                )
            elif self.species == 'op: singular: numeric method':
                assert discriminator is None
            elif self.species.startswith('op: discriminated by type'):
                assert isinstance(discriminator, Type)
            elif self.species == 'op: singular':
                assert discriminator is None or isinstance(discriminator, Type)
            elif self.species.startswith('bif:') or self.species == 'op: singular: host-defined':
                # The latter because HostMakeJobCallback has a default implementation
                assert discriminator is None
            else:
                assert 0, self.species

            assert isinstance(alg_defn.anode, ANode)
            assert alg_defn.anode.prod.lhs_s in [
                '{EMU_ALG_BODY}',
                '{EXPR}',
                '{ONE_LINE_ALG}',
                '{EE_RULE}',
                '{NAMED_OPERATION_INVOCATION}',
                '{RHSS}',
            ], alg_defn.anode.prod.lhs_s

            self.t_defns.append((discriminator,alg_defn.anode))

        (ln, _) = shared.convert_posn_to_linecol(header.node_at_end_of_header.end_posn)
        spec.info_for_line_[ln].afters.append(self)

    # ------------------------------------------------------

    def __str__(self):
        return f"""
            TypedAlgHeader:
                name: {self.name}
                species: {self.species}
                for : {self.for_param_type}
                params: {', '.join(
                    pn + ' : ' + str(pt)
                    for (pn, pt) in self.parameter_types.items())}
                returns: {self.return_type}
                # defns: {len(self.t_defns)}
        """

    # ------------------------------------------------------

    def lines(self, indentation, mode):
        assert mode in ['messages in algs and dls', 'dls w revised info']

        if self.name == 'Early Errors':
            # Don't bother, it's uninformative.
            return []

        lines = []
        latest_right_len = None
        # ---------------------------------------
        def put(line):
            lines.append(line)
        # ---------------------------------------
        def iput(line):
            # "iput" = "put with indentation"
            put(' '*indentation + line)
        # ---------------------------------------
        def iput_a_colon_b(left, right):
            padded_left = left.ljust(left_max_width)
            iput(f"    {padded_left} : {right}")
            nonlocal latest_right_len
            latest_right_len = len(right)
        # ---------------------------------------
        def iput_name_and_type(name, ptype):
            if ptype == T_0:
                if mode == 'messages in algs and dls':
                    iput_a_colon_b(name, 'TBD')
                else:
                    # show nothing
                    pass
            else:
                iput_a_colon_b(name, ptype.unparse())
        # ---------------------------------------
        def put_msg(msg):
            lead_up = indentation + 4 + left_max_width + 3
            put('-' * lead_up + '^' * latest_right_len)
            put('>>> ' + msg)
            put('')
        # ---------------------------------------

        iput('<!--')

        assert self.param_names is not None
        if len(self.param_names) == 0:
            iput("  parameters:")
            iput("    (none)")

        else:
            iput("  parameters:")
            left_max_width = max(len(param_name) for param_name in self.param_names)

            if True:
                if mode == 'messages in algs and dls':
                    params = self.initial_parameter_types
                else:
                    params = self.parameter_types

                for (pn, pt) in params.items():
                    iput_name_and_type(pn, pt)

                    # XXX Cases where operation_headers types the parameter as 'MathNonNegativeInteger_',
                    # but then that gets translated to 'Integer',
                    # so that's how it appears here.
                    # - ArrayCreate              : _length_
                    # - CodePointAt              : _position_
                    # - GetModifySetValueInBuffer: _byteIndex_
                    # - GetWaiterList            : _i_
                    # - RemoveWaiters            : _c_
                    # - ComposeWriteEventBytes   : _byteIndex_

                    if mode == 'messages in algs and dls':
                        p_node = self.fake_node_for_[pn]
                        if hasattr(p_node, 'errors'):
                            for msg in p_node.errors:
                                put_msg(msg)

        # -------------------------

        put('')
        iput("  returns:")
        left_max_width = max(len(name) for name in ["normal", "abrupt"])

        if True:
            if mode == 'messages in algs and dls':
                rt = self.initial_return_type
            else:
                rt = self.return_type

            if rt == T_TBD:
                abrupt_part = T_TBD
                normal_part = T_TBD
            else:
                (abrupt_part, normal_part) = rt.split_by(T_Abrupt)

            iput_name_and_type('normal', normal_part)
            iput_name_and_type('abrupt', abrupt_part)

            if mode == 'messages in algs and dls':
                p_node = self.fake_node_for_['*return*']
                if hasattr(p_node, 'errors'):
                    for msg in p_node.errors:
                        put_msg(msg)

        iput('-->')

        # -------------------------

        return lines

    # ------------------------------------------------------

    def make_env(self):
        e = Env()

        if self.for_param_name is not None:
            assert self.for_param_type is not None
            e.vars[self.for_param_name] = self.for_param_type
            e.parameter_names.add(self.for_param_name)

        for (pn, pt) in self.parameter_types.items():
            assert isinstance(pt, Type)
            e.vars[pn] = pt
            e.parameter_names.add(pn)

        e.vars['*return*'] = self.return_type

        return e

    # ----------------------------------------------------------------

    def change_declared_type(self, pname, new_t, tweak=False):
        if pname == '*return*':
            old_t = self.return_type
            self.return_type = new_t
        else:
            old_t = self.parameter_types[pname]
            self.parameter_types[pname] = new_t

        assert old_t != new_t

        verb = 'tweak' if tweak else 'change'
        change = "%s%s type of `%s` from `%s` to `%s`" % (
            g_level_prefix, verb, pname, old_t, new_t)
        node = self.fake_node_for_[pname]
        node._new_t = new_t
        install_error(node, change)

        #!!! print("EDIT: In a header for `%s`: %s" % (self.name, change))
        # if self.name == 'LabelledEvaluation' and pname == '_labelSet_': pdb.set_trace()

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

subtype_memo = {}
split_memo = {}

class Type(tuple):

    def set_of_types(self):
        return self.member_types if isinstance(self, UnionType) else frozenset([self])

    def __or__(A, B):
        if A == B: return A
        # check subtyping?
        A_members = A.set_of_types()
        B_members = B.set_of_types()
        u = maybe_UnionType(A_members | B_members)
        # print(A, '|', B, '=', u)
        return u

    # -----------------------------------------------------

    # @memoize()
    def is_a_subtype_of_or_equal_to(A, B):

        if (A,B) in subtype_memo:
            return subtype_memo[(A,B)]
        # No speed-up?

        if B == T_Top_: return True

        A_members = A.set_of_types()
        B_members = B.set_of_types()

        if T_TBD in A_members or T_TBD in B_members:
            result = False

        elif A_members <= B_members:
            result = True
        elif A_members > B_members:
            result = False

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

        subtype_memo[(A,B)] = result

        return result

    # -----------------------------------------------------

    def split_by(A, B):
        # Return a pair of types that partition A
        # (i.e., two disjoint types whose union is A):
        # one that is a subtype of (or equal to) B,
        # and one that is outside of B.
        # (Either can be T_0.)

        # if A == T_TBD and B == ListType(T_String): pdb.set_trace()

        if 0:
            (outside_B, inside_B, _) = compare_types(A, B)
            return (inside_B, outside_B)

        A_members = A.set_of_types()
        B_members = B.set_of_types()

        if (A,B) in split_memo:
            return split_memo[(A,B)]

        A_memtypes = A.set_of_types()
        B_memtypes = B.set_of_types()

        # A few cases that can be handled quickly:
        if A_memtypes == B_memtypes:
            inside_B  = A # or B
            outside_B = T_0

        elif A_memtypes <= B_memtypes:
            inside_B  = A
            outside_B = T_0

        elif B_memtypes <= A_memtypes:
            inside_B  = B
            outside_B = maybe_UnionType(A_memtypes - B_memtypes)

        else:
            # The general case:
            inside_B = set()
            outside_B = set()

            def recurse(A_subtypes, B_subtypes):
                for a in A_subtypes:
                    assert isinstance(a, Type)

                    # Treat T_TBD like Top
                    if a == T_TBD: a = T_Top_ # assert 0

                    if a.is_a_subtype_of_or_equal_to(B):
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
                                if a == ListType(T_character_) and bs_within_a == [ListType(T_code_point_)]:
                                    inside_B.add(ListType(T_code_point_))
                                    outside_B.add(ListType(T_code_unit_))
                                elif a == ListType(T_character_) and bs_within_a == [ListType(T_code_unit_)]:
                                    inside_B.add(ListType(T_code_unit_))
                                    outside_B.add(ListType(T_code_point_))
                                elif a == ListType(T_Tangible_) and bs_within_a == [ListType(T_Number)]:
                                    inside_B.add(ListType(T_Number))
                                    outside_B.add(ListType(T_Tangible_)) # XXX T_Tangible_ - T_Number (TypedArrayCreate)
                                else:
                                    assert 0
                            else:
                                tnode = tnode_for_type_[a]
                                a_imm_subtypes = [child.type for child in tnode.children]
                                recurse(a_imm_subtypes, bs_within_a)
                        else:
                            # no B_subtype is within `a`
                            # so `a` must be disjoint from B
                            outside_B.add(a)

            recurse(A_memtypes, B_memtypes)

            inside_B  = maybe_UnionType(inside_B)
            outside_B = maybe_UnionType(outside_B)

        print("%s :: %s  ===>  %s  ///  %s" %
            (A, B, outside_B, inside_B),
            file=split_types_f)

        result = (inside_B, outside_B)
        split_memo[(A,B)] = result
        return result


def member_is_a_subtype_or_equal(A, B):
    assert not isinstance(A, UnionType); assert A != T_TBD
    assert not isinstance(B, UnionType); assert B != T_TBD

    if A == B: return True

    if isinstance(A, NamedType):
        if isinstance(B, NamedType):
            A_tnode = tnode_for_type_[A]
            B_tnode = tnode_for_type_[B]
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
        elif isinstance(B, NamedType):
            return (T_List.is_a_subtype_of_or_equal_to(B))
        elif isinstance(B, ThrowType):
            return False
        else:
            assert 0, (A, B)

    elif isinstance(A, ThrowType):
        if isinstance(B, ThrowType):
            return (A.error_type.is_a_subtype_of_or_equal_to(B.error_type))
        elif isinstance(B, NamedType):
            return (T_throw_.is_a_subtype_of_or_equal_to(B))
        elif isinstance(B, ListType):
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
        elif isinstance(B, NamedType):
            return (T_proc_.is_a_subtype_of_or_equal_to(B))
        elif isinstance(B, ListType):
            return False
        else:
            assert 0, (A, B)

    elif isinstance(A, TupleType):
        if B == T_Abrupt:
            return False
        else:
            assert 0, (A, B)

    else:
        assert 0, (A, B)


    # --------------------------------------------------------------------------

class TBDType(Type):
    __slots__ = ()
    def __new__(cls):
        return tuple.__new__(cls, ('TBDType',))
    def __repr__(self): return "%s()" % self
    def __str__(self): return 'TBD'
    def unparse(self, parenthesuze=False): return 'TBD'

class NamedType(Type):
    __slots__ = ()
    def __new__(cls, name):
        assert isinstance(name, str)
        assert re.fullmatch(r'[\w -]+', name), name
        assert not name.startswith('a '), name
        return tuple.__new__(cls, ('NamedType', name))
    def __repr__(self): return "%s(%r)" % self
    def __str__(self): return self.name
    def unparse(self, parenthesize=False):
        if self.name.startswith('PTN_'):
            x = 'Parse Node for |%s|' % self.name.replace('PTN_','')
            if parenthesize: x = '(%s)' % x
            return x
        else:
            return self.name
    name = property(itemgetter(1))

class ListType(Type):
    __slots__ = ()
    def __new__(cls, element_type):
        return tuple.__new__(cls, ('ListType', element_type))
    def __repr__(self): return "%s(%r)" % self
    def __str__(self): return "List of %s" % str(self.element_type)
    def unparse(self, _=False): return "List of %s" % self.element_type.unparse(True)
    element_type = property(itemgetter(1))

class TupleType(Type):
    __slots__ = ()
    def __new__(cls, component_types):
        return tuple.__new__(cls, ('TupleType', component_types))
    def __repr__(self): return "%s(%r)" % self
    def __str__(self): return "(%s)" % ', '.join(str(t) for t in self.component_types)
    def unparse(self, _=False): return "(%s)" % ', '.join(t.unparse(True) for t in self.component_types)
    component_types = property(itemgetter(1))

class ThrowType(Type):
    __slots__ = ()
    def __new__(cls, error_type):
        return tuple.__new__(cls, ('ThrowType', error_type))
    def __repr__(self): return "%s(%r)" % self
    def __str__(self): return "throw_(%s)" % str(self.error_type)
    def unparse(self, _=False): return "throw_ *%s*" % self.error_type.unparse(True)
    error_type = property(itemgetter(1))

class ProcType(Type):
    __slots__ = ()
    def __new__(cls, param_types, return_type):
        return tuple.__new__(cls, ('ProcType', tuple(param_types), return_type))
    def __repr__(self): return "%s(%r, %r)" % self
    def __str__(self):
        if self == T_Continuation:
            return "Continuation"
        elif self == T_Matcher:
            return "Matcher"
        elif self == T_ReadModifyWrite_modification_closure:
            return "ReadModifyWrite_modification_closure"
        elif self == T_RegExpMatcher_:
            return "RegExpMatcher_"
        else:
            return "(%s -> %s)" % (self.param_types, self.return_type)
    def unparse(self, _=False): return str(self)

    param_types = property(itemgetter(1))
    return_type = property(itemgetter(2))

class UnionType(Type):
    # A union of (non-union) types.
    # Must satisfy the constraint that no member-type
    # is a subtype or supertype of any other member-type.
    # (XXX: Should check that in __new__.)

    __slots__ = ()
    def __new__(cls, member_types):
        assert len(member_types) != 1
        for type in member_types:
            assert not isinstance(type, UnionType)
        return tuple.__new__(cls, ('UnionType', frozenset(member_types)))
    def __repr__(self): return "%s(%r)" % self
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

        x = ' | '.join(sorted(
            member_type.unparse()
            for member_type in member_types
        ))
        if parenthesize: x = '(' + x + ')'
        return prefix + x

    member_types = property(itemgetter(1))

T_0 = UnionType([])

def maybe_UnionType(member_types):
    assert not isinstance(member_types, Type)
    if len(member_types) == 1:
        return list(member_types)[0]
    else:
        return UnionType(member_types)

# ------------------------------------------------------------------------------

def type_for_environment_record_kind(kind):
    return NamedType(kind.source_text() + ' Environment Record')

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
    type = NamedType(type_name)
    if optionality: type = type | T_not_in_node
    return type

# ------------------------------------------------------------------------------

named_type_hierarchy = {
    'Top_': {
        'Abrupt' : {
            'continue_': {},
            'break_': {},
            'return_': {},
            'throw_': {},
        },
        'Normal': {
            'Absent': { # not sure this is at the right place in the hierarchy.
                'not_passed': {},    # for an optional parameter
                'not_in_node': {},   # for an optional child of a node
                'not_set': {},       # for a metavariable that might not be initialized
                'not_returned': {},  # for when control falls off the end of an operation
            },
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
                        'InfiniteNumber_': {},
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
                        'constructor_object_': {}, # XXX This is actually orthogonal to Proxy/Bound/other
                        'Proxy_exotic_object_': {},
                        'bound_function_exotic_object_': {},
                        'other_function_object_': {},
                    },
                    'other_Object_': {},
                },
            },
            'Intangible_': {
                'AssignmentTargetType_': {},
                'CharSet': {},
                'ClassElementKind_': {},
                'Data Block': {},
                'FunctionKind2_': {},
                'event_pair_': {},
                'IEEE_binary32_': {},
                'IEEE_binary64_': {},
                'IterationKind_': {},
                'IteratorKind_': {},
                'LangTypeName_': {},
                'LhsKind_': {},
                'List': {},
                'MatchResult': {
                    'State': {},
                    'match_failure_': {},
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
                'NotMatched_' : {},
                'Parse Node' : {
                    'PTN_ForBinding': {},
                    'PTN_Script': {},
                    'PTN_Pattern': {},
                },
                'PreferredTypeHint_': {},
                'Private Name': {},
                'PrivateElementKind_': {},
                'PropertyKeyKind_': {},
                'Range': {},
                'Record': {
                    'Agent Record': {},
                    'Agent Events Record': {},
                    'AsyncGeneratorRequest Record': {},
                    'Chosen Value Record': {},
                    'ClassFieldDefinition Record': {},
                    'ClassStaticBlockDefinition Record': {},
                    'CharacterClassResultRecord_': {},
                    'Environment Record': {
                        'Declarative Environment Record': {
                            'Function Environment Record': {},
                            'Module Environment Record': {},
                        },
                        'Object Environment Record': {},
                        'Global Environment Record': {},
                    },
                    'ExportEntry Record': {},
                    'ExportResolveSet_Record_': {},
                    'FinalizationRegistryCellRecord_': {},
                    'GlobalSymbolRegistry Record': {},
                    'ImportEntry Record': {},
                    'ImportMeta_record_': {},
                    'Intrinsics Record': {},
                    'Iterator Record': {},
                    'JSON Serialization Record': {},
                    'Job_record_': {},
                    'JobCallback Record': {},
                    'MapData_record_': {},
                    'Match Record': {},
                    'Module Record': {
                        'Cyclic Module Record': {
                            'Source Text Module Record': {},
                            'other Cyclic Module Record': {},
                        },
                        'other Module Record': {},
                    },
                    'PrivateElement': {},
                    'PrivateEnvironment Record': {},
                    'PromiseCapability Record': {},
                    'PromiseReaction Record': {},
                    'Property Descriptor': {
                        # subtypes data and accessor and generic?
                    },
                    'QuantifierPrefixResultRecord_': {},
                    'QuantifierResultRecord_': {},
                    'Realm Record': {},
                    'Reference Record': {},
                    'RegExp Record': {},
                    'ResolvedBinding Record': {},
                    'ResolvingFunctions_record_': {},
                    'Script Record': {},
                    #
                    'boolean_value_record_': {},
                    'candidate execution': {},
                    'CodePointAt_record_': {},
                    'event_': {
                        'Shared Data Block event': {
                            'ReadModifyWriteSharedMemory event': {},
                            'ReadSharedMemory event': {},
                            'WriteSharedMemory event': {},
                        },
                        'Synchronize event': {},
                        'host-specific event': {},
                    },
                    'integer_value_record_': {},
                    'methodDef_record_': {},
                    'templateMap_entry_': {},
                },
                # 'Reference': {}, # 2085
                'RegExpDirection_': {},
                'Relation': {},
                'Set': {},
                'Shared Data Block': {},
                'SharedMemory_ordering_': {},
                'SlotName_': {},
                'TildeAllButDefault_': {},
                'TildeAll_': {},
                'TildeAmbiguous_': {},
                'TildeNamespaceObject_': {},
                'TildeNamespace_': {},
                'TildeUnused_': {},
                'TrimString_where_': {},
                'TypedArray_element_type_': {},
                'Unresolvable_': {},
                'WaiterList' : {},
                'agent_signifier_' : {},
                'alg_steps': {},
                # 'character_': {
                #     # 'code_unit_': {},
                #     'code_point_': {},
                # },
                'completion_kind_': {},
                'constructor_kind_': {},
                'empty_': {},
                'iteration_result_kind_': {},
                'execution context': {},
                'generator_state_': {},
                'grammar_symbol_': {},
                'host_defined_': {},
                'integrity_level_': {},
                'module_record_status_': {},
                'numeric_primitive_type_': {},
                'proc_': {},
                'promise_state_': {},
                'property_': {
                    'data_property_': {},
                    'accessor_property_': {},
                },
                'settlement_type_': {},
                'this_binding_status_': {},
                'this_mode': {},
                'this_mode2_': {},
                'tuple_': {},
                'other_': {},
            },
        },
    }
}

tnode_for_type_ = {}

class TNode:
    def __init__(self, type, parent):
        self.type = type
        self.parent = parent

        self.children = []

        if parent is None:
            self.level = 0
        else:
            self.level = parent.level + 1
            parent.children.append(self)

        tnode_for_type_[type] = self

def traverse(typesdict, p):
    for (type_name, subtypesdict) in typesdict.items():
    # sorted(typesdict.items(), key=lambda tup: 1 if tup[0] == 'List' else 0):
        assert isinstance(type_name, str)
        t = NamedType(type_name)
        #
        variable_name = 'T_' + type_name.replace(' ', '_')
        globals()[variable_name] = t
        #
        tnode = TNode(t, p)
        traverse(subtypesdict, tnode)

stderr("initializing the type hierarchy...")
traverse(named_type_hierarchy, None)

troot = tnode_for_type_[T_Top_]

def ensure_tnode_for(type):
    assert isinstance(type, Type)
    if type in tnode_for_type_:
        return tnode_for_type_[type]
    else:
        if isinstance(type, NamedType):
            assert 0, type
        elif isinstance(type, ThrowType):
            parent_type = T_throw_
        elif isinstance(type, ListType):
            parent_type = T_List # XXX but this fails to capture subtypes within
        elif isinstance(type, ProcType):
            parent_type = T_proc_
        elif isinstance(type, TupleType):
            parent_type = T_tuple_
        else:
            assert 0, type
        return TNode(type, tnode_for_type_[parent_type])
        # which has the side-effect of adding it to tnode_for_type_

ensure_tnode_for( ListType(T_other_) )
ensure_tnode_for( ProcType((), T_other_) )
ensure_tnode_for( ThrowType(T_other_) )
ensure_tnode_for( TupleType((T_other_,)) )

# ------------------------------------------------------------------------------

T_TBD = TBDType()

T_character_ = T_code_unit_ | T_code_point_

T_MathNonNegativeInteger_ = T_MathInteger_ # for now

T_Continuation    = ProcType([T_State                ], T_MatchResult)
T_Matcher         = ProcType([T_State, T_Continuation], T_MatchResult)
T_RegExpMatcher_  = ProcType([ListType(T_character_), T_MathNonNegativeInteger_], T_MatchResult)
T_Job             = ProcType([                       ], T_Tangible_ | T_empty_ | T_throw_)

T_ReadModifyWrite_modification_closure = ProcType([ListType(T_MathInteger_), ListType(T_MathInteger_)], ListType(T_MathInteger_))

T_captures_entry_ = T_Range | T_Undefined
T_captures_list_  = ListType(T_captures_entry_)

T_Unicode_code_points_ = ListType(T_code_point_)

T_Integer_Indexed_object_ = T_TypedArray_object_

# ------------------------------------------

def type_for_ERROR_TYPE(error_type):
    st = error_type.source_text()
    assert st.startswith('*')
    assert st.endswith('*')
    error_type_name = st[1:-1]
    return NamedType(error_type_name)

def type_for_TYPE_NAME(type_name):
    assert isinstance(type_name, ANode)
    assert type_name.prod.lhs_s == '{TYPE_NAME}'
    st = type_name.source_text()
    return NamedType(st)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def convert_nature_node_to_type(nature_node):
    if nature_node is None: return T_TBD

    return convert_value_description(nature_node)

# --------------------------------------

def convert_value_description(value_description):

    assert value_description.prod.lhs_s == '{VALUE_DESCRIPTION}'

    vd_st = value_description.source_text()
    if vd_st in nature_to_type:
        return nature_to_type[vd_st]

    p = str(value_description.prod)
    if p == '{VALUE_DESCRIPTION} : {VAL_DESC}':
        [val_desc] = value_description.children
        return convert_val_desc(val_desc)

    elif p in [
        '{VALUE_DESCRIPTION} : either {VAL_DESC} or {VAL_DESC}',
        '{VALUE_DESCRIPTION} : either {VAL_DESC}, or {VAL_DESC}',
        '{VALUE_DESCRIPTION} : either {VAL_DESC}, {VAL_DESC}, or {VAL_DESC}',
        '{VALUE_DESCRIPTION} : either {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, or {VAL_DESC}',
        '{VALUE_DESCRIPTION} : {VAL_DESC} or {VAL_DESC}',
        '{VALUE_DESCRIPTION} : {VAL_DESC}, {VAL_DESC}, or {VAL_DESC}',
        '{VALUE_DESCRIPTION} : {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, or {VAL_DESC}',
        '{VALUE_DESCRIPTION} : {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, or {VAL_DESC}',
    ]:
        t = T_0
        for val_desc in value_description.children:
            t |= convert_val_desc(val_desc)
        return t

    elif p == '{VALUE_DESCRIPTION} : {VAL_DESC}, but not {VALUE_DESCRIPTION}':
        [pos_desc, neg_desc] = value_description.children
        # t = convert_val_desc(pos_desc) - convert_value_description(neg_desc)
        text = value_description.source_text()
        if text == 'an ECMAScript language value, but not a Number':
            t = T_Undefined | T_Null | T_Boolean | T_BigInt | T_String | T_Symbol | T_Object
        elif text == 'an ECMAScript language value, but not *undefined* or *null*':
            t = T_Boolean | T_Number | T_BigInt | T_String | T_Symbol | T_Object
        elif text == 'an ECMAScript language value, but not a TypedArray':
            t = T_Tangible_
        elif text == 'a Number, but not *NaN*':
            t = T_FiniteNumber_ | T_InfiniteNumber_
        elif text == 'an Object, but not a TypedArray or an ArrayBuffer':
            t = T_Object
        else:
            assert 0, text
        return t

    else:
        assert 0, repr(p)

# --------------------------------------

def convert_val_desc(val_desc):
    assert val_desc.prod.lhs_s == '{VAL_DESC}'

    if val_desc.prod.rhs_s == '{backticked_oth}':
        return T_Unicode_code_points_

    if val_desc.prod.rhs_s == '{LITERAL}':
        [literal] = val_desc.children
        if literal.prod.rhs_s == '{STR_LITERAL}':
            return T_String

    if val_desc.prod.rhs_s == 'an? {nonterminal} Parse Node':
        [nont] = val_desc.children
        return ptn_type_for(nont)

    if val_desc.prod.rhs_s == 'a normal completion containing {VALUE_DESCRIPTION}':
        [value_description] = val_desc.children
        return convert_value_description(value_description)

    nature = val_desc.source_text()
    try:
        t = nature_to_type[nature]
    except KeyError:
        val_desc.printTree(f=sys.stderr)
        assert 0
        print(nature, file=un_f)
        t = T_TBD

    assert isinstance(t, Type), nature
    return t

# ------------------------------------------------------------------------------

def convert_nature_to_type(nature):
    assert 'VAR' not in nature, nature

    try:
        t = nature_to_type[nature]
        assert isinstance(t, Type), nature
    except KeyError:
        print(nature, file=un_f)
        t = NamedType(nature)

    return t

nature_to_type = {
        'unknown': T_TBD,
        'anything': T_host_defined_,

        'any value except a Completion Record': T_Tangible_ | T_Intangible_,

    # 5.1.4 The Syntactic Grammar
        'a grammar symbol'                                : T_grammar_symbol_,
        'a nonterminal in one of the ECMAScript grammars' : T_grammar_symbol_,

        'Parse Node'                                                            : T_Parse_Node,
        'a Parse Node'                                                          : T_Parse_Node,

    # 5.2.5 Mathematical Operations
        'a mathematical value'      : T_MathReal_,
        'an integer'                : T_MathInteger_,
        'a non-negative integer'    : T_MathNonNegativeInteger_, # currently mapped to MathInteger_
        'a positive integer'        : T_MathNonNegativeInteger_,
        '0 or 1'                    : T_MathNonNegativeInteger_,
        'a non-negative integer that is evenly divisible by 4' : T_MathNonNegativeInteger_,
        'an integer in the inclusive interval from 2 to 36': T_MathNonNegativeInteger_,
        '+&infin;'                  : T_MathPosInfinity_,
        '-&infin;'                  : T_MathNegInfinity_,

    # 5.2.6 Value Notation
        '~empty~' : T_empty_,

        '~ambiguous~' : T_TildeAmbiguous_,
        '~unused~'    : T_TildeUnused_,

    # 6.1 ECMAScript language types

        'an ECMAScript language value'                       : T_Tangible_,
        'a value'                                            : T_Tangible_,

    # 6.1.1 The Undefined Type
        '*undefined*': T_Undefined,

    # 6.1.2 The Null Type
        '*null*': T_Null,

    # 6.1.3 The Boolean Type
        'a Boolean' : T_Boolean,
        '*false*'   : T_Boolean,
        '*true*'    : T_Boolean,

    # 6.1.4 The String Type
        'a String'                  : T_String,
        '*"reject"* or *"handle"*'  : T_String,
        'a String which is the name of a TypedArray constructor in <emu-xref href="#table-the-typedarray-constructors"></emu-xref>': T_String,

        'a code unit' : T_code_unit_,

    # 6.1.5 The Symbol Type
        'a Symbol' : T_Symbol,

    # 6.1.6.1 The Number Type
        'a Number'       : T_Number,

        'an integral Number' : T_IntegralNumber_,

    # 6.1.6.2 The BigInt Type
        'a BigInt'    : T_BigInt,

    # 6.1.7 The Object Type
        'an Object'                                                      : T_Object,
        'an Object that conforms to the <i>IteratorResult</i> interface' : T_Object,
        'an Object that has a [[StringData]] internal slot'              : T_Object,
        'an initialized RegExp instance'                                 : T_Object,

        'an internal slot name' : T_SlotName_,

        # function_: an object with a [[Call]] internal method
        'a function object'                                           : T_function_object_,

        # constructor_: an object with a [[Construct]] internal method
        'a constructor'          : T_constructor_object_,

        'a property key'                 : T_String | T_Symbol,
        'a property key or Private Name' : T_String | T_Symbol | T_Private_Name,

    # 6.2.1 The List and Record Specification Types
        'a List'                                      : T_List,
        'a List of Cyclic Module Records'             : ListType(T_Cyclic_Module_Record),
        'a List of ECMAScript language values'        : ListType(T_Tangible_),
        'a List of ExportEntry Records'               : ListType(T_ExportEntry_Record),
        'a List of ImportEntry Records'               : ListType(T_ImportEntry_Record),
        'a List of Parse Nodes'                       : ListType(T_Parse_Node),
        'a List of PromiseReaction Records'           : ListType(T_PromiseReaction_Record),
        'a List of Records that have [[Module]] and [[ExportName]] fields': ListType(T_ExportResolveSet_Record_),
        'a List of Records with fields [[Key]] (a property key) and [[Value]] (an ECMAScript language value)': ListType(T_ImportMeta_record_),
        'a List of Source Text Module Records'        : ListType(T_Source_Text_Module_Record),
        'a List of Strings'                           : ListType(T_String),
        'a List of agent signifiers'                  : ListType(T_agent_signifier_),
        'a List of byte values'                       : ListType(T_MathInteger_),
        'a List of characters'                        : ListType(T_character_),
        'a List of either Match Records or *undefined*': ListType(T_Match_Record | T_Undefined),
        'a List of either Strings or *null*'          : ListType(T_String | T_Null),
        'a List of either Strings or *undefined*'     : ListType(T_String | T_Undefined),
        'a List of internal slot names'               : ListType(T_SlotName_),
        'a List of names of ECMAScript Language Types': ListType(T_LangTypeName_),
        'a List of names of internal slots'           : ListType(T_SlotName_),
        'a List of property keys'                     : ListType(T_String | T_Symbol),
        'a List of |ClassElement| Parse Nodes'        : ListType(ptn_type_for('ClassElement')),
        'a List of |GroupSpecifier| Parse Nodes'      : ListType(ptn_type_for('GroupSpecifier')),
        'a non-empty List of *SyntaxError* objects'   : ListType(T_SyntaxError),
        'a possibly empty List, each of whose elements is a String or *undefined*': ListType(T_String | T_Undefined),

    # 6.2.2 The Set and Relation Specification Types

    # 6.2.3 The Completion Record Specification Type
        'a Completion Record': T_Abrupt | T_Normal,

        'a normal completion'            : T_Normal,
        'an abrupt completion'           : T_Abrupt,
        'a return completion'            : T_return_,
        'a throw completion'             : T_throw_,

    # 6.2.4 Reference Record
        'a Reference Record' : T_Reference_Record,
        'a Super Reference Record' : T_Reference_Record,

    # 6.2.5 Property Descriptor
        'a Property Descriptor' : T_Property_Descriptor,

    # 6.2.7 Abstract Closure
        'an Abstract Closure': T_proc_,
        'an Abstract Closure with no parameters': ProcType([], T_Top_),
        'an Abstract Closure with two parameters': ProcType([T_Tangible_, T_Tangible_], T_Number | T_throw_),
        'an Abstract Closure that takes a List of characters and a non-negative integer and returns a MatchResult': T_RegExpMatcher_,

    # 6.2.8 Data Block
        'a Data Block'        : T_Data_Block,
        'a Shared Data Block' : T_Shared_Data_Block,
        # is it a subtype of Data Block? Doesn't seem to be treated that way

    # 6.2.9 The PrivateElement Specification Type
        'a PrivateElement': T_PrivateElement,

    # 6.2.10 The ClassFieldDefinition Record Specification Type
        'a ClassFieldDefinition Record': T_ClassFieldDefinition_Record,

    # 6.2.11 Private Name
        'a Private Name': T_Private_Name,

    # 6.2.12 ClassStaticBlockDefinition
        'a ClassStaticBlockDefinition Record': T_ClassStaticBlockDefinition_Record,

    # 7.1.1 ToPrimitive
        '~string~ or ~number~' : T_PreferredTypeHint_,

    # 7.3.15 SetIntegrityLevel
        '~sealed~ or ~frozen~' : T_integrity_level_,

    # 7.4.1 Iterator Records
        'an Iterator Record': T_Iterator_Record,

    # 8.5.4 Static Semantics: AssignmentTargetType
        '~simple~ or ~invalid~' : T_AssignmentTargetType_,

    # (6.2.6 The Environment Record Specification Type)
    # 9.1 Environment Records
        'an Environment Record'            : T_Environment_Record,
        'a Declarative Environment Record' : T_Declarative_Environment_Record,
        'a Global Environment Record'      : T_Global_Environment_Record,
        'a Module Environment Record'      : T_Module_Environment_Record,
        'a Function Environment Record'    : T_Function_Environment_Record,
        'an Object Environment Record'     : T_Object_Environment_Record,

    # 9.2 PrivateEnvironment Records
        'a PrivateEnvironment Record': T_PrivateEnvironment_Record,

    # 9.3 Realms
        'a Realm Record' : T_Realm_Record,

    # 9.4 Execution Contexts
        'an execution context' : T_execution_context,

    # 9.5 Jobs etc
        'a Job Abstract Closure' : T_Job,

    # 9.5.1 JobCallback Record
        'a JobCallback Record': T_JobCallback_Record,

    # 9.7 Agents
        'an agent signifier' : T_agent_signifier_,

    # 10.1 Ordinary Object
        'an ordinary object' : T_Object,

    # 10.2 ECMAScript Function Objects
    # 10.3 Built-in Function Objects
    # 20.2 Function Objects
        'an ECMAScript function object'                               : T_function_object_,
        'an ECMAScript function object or a built-in function object' : T_function_object_,
        'an ECMAScript function'                                      : T_function_object_,
        'a built-in function object'                                  : T_function_object_,

    # 10.2.3 OrdinaryFunctionCreate
        '~lexical-this~ or ~non-lexical-this~': T_this_mode2_,

    # 10.3.3 CreateBuiltinFunction
        'a set of algorithm steps' : T_alg_steps,
        "some other definition of a function's behaviour provided in this specification": T_alg_steps,

    # 10.4.1 Bound Function Exotic Objects
        'a bound function exotic object' : T_bound_function_exotic_object_,

    # 10.4.2 Array Exotic Objects
    # 23.1 Array Objects
        'an Array' : T_Array_object_,
        'an Array exotic object' : T_Array_object_,

    # 10.4.3 String Exotic Objects
        'a String exotic object' : T_String_exotic_object_,

    # 10.4.4 Arguments Exotic Objects
        'an arguments exotic object' : T_Object,

    # 10.4.5 Integer-Indexed Exotic Objects
        'an Integer-Indexed exotic object': T_Integer_Indexed_object_,

    # 10.4.6 Module Namespace Exotic Objects
        'a Module Namespace Object'        : T_Object,
        'a module namespace exotic object' : T_Object,

    # 10.4.7 Immutable Prototype Exotic Objects
        'an immutable prototype exotic object' : T_Object,

    # 10.5 Proxy Object ...
        'a Proxy exotic object': T_Proxy_exotic_object_,

    # 11.1 Source Text
        'a code point'         : T_code_point_,
        'a Unicode code point' : T_code_point_,

        'source text'                       : T_Unicode_code_points_,
        '`&amp;`, `^`, or `|`'              : T_Unicode_code_points_,
        'ECMAScript source text'            : T_Unicode_code_points_,
        'a sequence of Unicode code points' : T_Unicode_code_points_,
        '`**`, `*`, `/`, `%`, `+`, `-`, `&lt;&lt;`, `&gt;&gt;`, `&gt;&gt;&gt;`, `&amp;`, `^`, or `|`': T_Unicode_code_points_,
        'a List of code points'             : T_Unicode_code_points_,

    # 11.1.4 Static Semantics: CodePointAt
        'a Record with fields [[CodePoint]] (a code point), [[CodeUnitCount]] (a positive integer), and [[IsUnpairedSurrogate]] (a Boolean)': T_CodePointAt_record_,

    # 14.7.5.6 ForIn/OfHeadEvaluation
        '~enumerate~ or ~iterate~': T_IterationKind_,
        '~enumerate~, ~iterate~, or ~async-iterate~' : T_IterationKind_,

    # 14.7.5.7 ForIn/OfBodyEvaluation
        '~assignment~, ~varBinding~, or ~lexicalBinding~' : T_LhsKind_,

        '~sync~ or ~async~' : T_IteratorKind_,

    # 14.7.5.10 For-In Iterator Objects
        'a For-In Iterator' : T_Iterator_object_,

    # 15.4.4 Runtime Semantics: DefineMethod
        'a Record with fields [[Key]] (a property key) and [[Closure]] (a function object)': T_methodDef_record_,

    # 15.7.2 Static Semantics: ClassElementKind
        '~ConstructorMethod~'   : T_ClassElementKind_,
        '~NonConstructorMethod~': T_ClassElementKind_,

    # 16.1.4 Script Records
        'a Script Record' : T_Script_Record,

    # 16.2.1.4 Abstract Module Records
        'a Module Record'                                    : T_Module_Record,
        'an instance of a concrete subclass of Module Record': T_Module_Record,
        'a Cyclic Module Record'                             : T_Cyclic_Module_Record,
        'a Source Text Module Record'                        : T_Source_Text_Module_Record,
        'a ResolvedBinding Record'                           : T_ResolvedBinding_Record,

    # 20.1.2.11.1 GetOwnPropertyKeys
        '~string~ or ~symbol~' : T_PropertyKeyKind_,

    # 20.2.1.1.1 CreateDynamicFunction
        '~normal~, ~generator~, ~async~, or ~asyncGenerator~' : T_FunctionKind2_,

    # 21.4.1.1 TimeValues
        'a time value'       : T_IntegralNumber_,
        # time value is defined to be 'IntegralNumber_ | NaN_Number_',
        # but the only use (so far) is for LocalTime()'s _t_ param,
        # which probably shouldn't accept NaN.
        # I.e., it should be marked "a *finite* time value".

    # 22.1.3.30.1 TrimString
        '~start~ or ~end~'               : T_TrimString_where_,
        '~start~, ~end~, or ~start+end~' : T_TrimString_where_,

    # 22.2.1 Patterns
        'a character' : T_code_unit_ | T_code_point_,

        'a Unicode property name'  : T_Unicode_code_points_,
        'a Unicode property value' : T_Unicode_code_points_,

    # 22.2.2.1 Notation:
        'a CharSet'      : T_CharSet,
        'a State'        : T_State,
        'a Continuation' : T_Continuation,
        'a Matcher'      : T_Matcher,
        'a Match Record' : T_Match_Record,
        'a MatchResult'  : T_MatchResult,
        'a RegExp Record': T_RegExp_Record,

        'a Record with fields [[CharSet]] (a CharSet) and [[Invert]] (a Boolean)' : T_CharacterClassResultRecord_,
        'a Record with fields [[Min]] (a non-negative integer) and [[Max]] (a non-negative integer or +&infin;)': T_QuantifierPrefixResultRecord_,
        'a Record with fields [[Min]] (a non-negative integer), [[Max]] (a non-negative integer or +&infin;), and [[Greedy]] (a Boolean)': T_QuantifierResultRecord_,
        '~forward~ or ~backward~' : T_RegExpDirection_,

    # 23.2 TypedArray Objects
        'a TypedArray'       : T_TypedArray_object_,

        'a TypedArray element type' : T_TypedArray_element_type_,

    # 25.1 ArrayBuffer Objects
    # 25.2 SharedArrayBuffer Objects

        # ArrayBuffer_: an object with an [[ArrayBufferData]] internal slot
        'an ArrayBuffer'                        : T_ArrayBuffer_object_,
        'a SharedArrayBuffer'                   : T_SharedArrayBuffer_object_,
        'an ArrayBuffer or SharedArrayBuffer'   : T_ArrayBuffer_object_ | T_SharedArrayBuffer_object_,
        'an ArrayBuffer or a SharedArrayBuffer' : T_ArrayBuffer_object_ | T_SharedArrayBuffer_object_,

    # 25.1.1 [ArrayBuffer Objects] Notation
        'a read-modify-write modification function': T_ReadModifyWrite_modification_closure,

    # 25.1.2.10 GetValueFromBuffer
        '~SeqCst~ or ~Unordered~'          : T_SharedMemory_ordering_,

    # 25.1.2.12 SetValueInBuffer
        '~SeqCst~, ~Unordered~, or ~Init~' : T_SharedMemory_ordering_,

    # 25.4.1 WaiterList Objects
        'a WaiterList' : T_WaiterList,

    # 25.5.2.1
        'a JSON Serialization Record' : T_JSON_Serialization_Record,

    # 26.1 WeakRef Objects
        'a WeakRef': T_WeakRef_object_,

    # 26.2 FinalizationRegistry Objects
        'a FinalizationRegistry' : T_FinalizationRegistry_object_,

    # 27.1.1.2 The Iterator Interface
        'an Iterator'       : T_Iterator_object_,

        '~key+value~ or ~value~'         : T_iteration_result_kind_,
        '~key+value~, ~key~, or ~value~' : T_iteration_result_kind_,
        '~key~, ~value~, or ~key+value~' : T_iteration_result_kind_,

    # 27.2 Promise Objects
        'a Promise'    : T_Promise_object_,

    # 27.2.1.1 PromiseCapability Record
        'a PromiseCapability Record'    : T_PromiseCapability_Record,
        'a PromiseCapability Record for an intrinsic %Promise%': T_PromiseCapability_Record,

    # 27.2.1.2 PromiseReaction Records
        'a PromiseReaction Record' : T_PromiseReaction_Record,

    # 27.2.1.3 CreateResolvingFunctions
        'a Record with fields [[Resolve]] (a function object) and [[Reject]] (a function object)' : T_ResolvingFunctions_record_,

    # 27.2.2.1 NewPromiseReactionJob
        'a Record with fields [[Job]] (a Job Abstract Closure) and [[Realm]] (a Realm Record or *null*)': T_Job_record_,

    # 27.2.2.2 NewPromiseResolveThenableJob
        'a Record with fields [[Job]] (a Job Abstract Closure) and [[Realm]] (a Realm Record)': T_Job_record_,

    # 27.5 Generator Objects
        'a Generator' : T_Iterator_object_,

    # 27.5.3.2 GeneratorValidate
        'either ~suspendedStart~, ~suspendedYield~, or ~completed~' : T_generator_state_,

    # 27.5.3.5 GetGeneratorKind
        '~non-generator~, ~sync~, or ~async~' : T_IteratorKind_,

    # 27.6 AsyncGenerator Objects
        'an AsyncGenerator': T_AsyncGenerator_object_,

    # 29.1 Memory Model Fundamentals
        'a ReadSharedMemory or ReadModifyWriteSharedMemory event':
            T_ReadSharedMemory_event | T_ReadModifyWriteSharedMemory_event,
        'a List of either WriteSharedMemory or ReadModifyWriteSharedMemory events':
            ListType(T_WriteSharedMemory_event | T_ReadModifyWriteSharedMemory_event),

    # 29.4 Candidate Executions
        'a candidate execution': T_candidate_execution,
        'an execution'         : T_candidate_execution, # ???

        'an event in SharedDataBlockEventSet(_execution_)': T_Shared_Data_Block_event,

    # 29.5 Abstract Operations for the Memory Model
        'a Set of events' : T_Set,

}

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

type_tweaks_tuples = [
    ('AsyncGeneratorEnqueue'                    , '_completion_'           , T_Abrupt | T_Normal   , T_Tangible_ | T_return_ | T_throw_),
    ('AsyncGeneratorUnwrapYieldResumption'      , '_resumptionValue_'      , T_Abrupt | T_Normal   , T_Tangible_ | T_return_ | T_throw_),
    ('AsyncIteratorClose'                       , '_completion_'           , T_Abrupt | T_Normal   , T_Tangible_ | T_empty_ | T_throw_),
    ('IteratorClose'                            , '_completion_'           , T_Normal | T_Abrupt   , T_Tangible_ | T_empty_ | T_throw_),
    ('MV'                                       , '*return*'               , T_TBD                 , T_MathInteger_),
    ('PromiseResolve'                           , '_C_'                    , T_constructor_object_ , T_Object),
    ('Day'                                      , '_t_'                    , T_TBD                 , T_FiniteNumber_ | T_InfiniteNumber_),
    ('TimeWithinDay'                            , '_t_'                    , T_TBD                 , T_FiniteNumber_ | T_InfiniteNumber_),
    ('DaysInYear'                               , '_y_'                    , T_TBD                 , T_FiniteNumber_ | T_InfiniteNumber_),
    ('DayFromYear'                              , '_y_'                    , T_TBD                 , T_FiniteNumber_ | T_InfiniteNumber_),
    ('TimeFromYear'                             , '_y_'                    , T_TBD                 , T_FiniteNumber_ | T_InfiniteNumber_),
    ('YearFromTime'                             , '_t_'                    , T_TBD                 , T_FiniteNumber_ | T_InfiniteNumber_),
    ('MonthFromTime'                            , '_t_'                    , T_TBD                 , T_FiniteNumber_ | T_InfiniteNumber_),
    ('DateFromTime'                             , '_t_'                    , T_TBD                 , T_FiniteNumber_ | T_InfiniteNumber_),
    ('WeekDay'                                  , '_t_'                    , T_TBD                 , T_FiniteNumber_ | T_InfiniteNumber_),
    ('HourFromTime'                             , '_t_'                    , T_TBD                 , T_FiniteNumber_ | T_InfiniteNumber_),
    ('MinFromTime'                              , '_t_'                    , T_TBD                 , T_FiniteNumber_ | T_InfiniteNumber_),
    ('SecFromTime'                              , '_t_'                    , T_TBD                 , T_FiniteNumber_ | T_InfiniteNumber_),
    ('msFromTime'                               , '_t_'                    , T_TBD                 , T_FiniteNumber_ | T_InfiniteNumber_),
]
class TypeTweaks:
    def __init__(self):
        self.tweaks = []
        self.n_uses = 0

type_tweaks_for_op_ = defaultdict(TypeTweaks)
for tweak_tuple in type_tweaks_tuples:
    [op_name, p_name, old_t, new_t] = tweak_tuple
    type_tweaks_for_op_[op_name].tweaks.append( tweak_tuple )

def print_unused_type_tweaks():
    f = shared.open_for_output('unused_type_tweaks')
    for (op_name, type_tweaks) in type_tweaks_for_op_.items():
        if type_tweaks.n_uses == 0:
            print(op_name, file=f)

# UpdateEmpty: _completionRecord_, *return

# InitializeReferencedBinding: _V_ and _W_ can be Abrupt
# InitializeBoundName return?
# ToPrimitive _PreferredType_
# OrdinaryHasInstance: _C_, _O_
# IteratorNext: _value_
# IteratorStep: return
# LoopContinues: _completion_
# PerformEval: _x_ + return
# RegExpInitialize: _pattern_, _flags_
# RegExpCreate: _P_, _F_
# IteratorDestructuringAssignmentEvaluation: return
# KeyedDestructuringAssignmentEvaluation: return
# LabelledEvaluation: return
# ForBodyEvaluation: return
# ForIn/OfBodyEvaluation: return
# BoundNames: return


# ------------------------------------------------------------------------------

# memoize
def union_of_types(types):
    if len(types) == 0: return T_0

    types1 = set(types)

    # Treat T_TBD like T_0,
    # i.e. the union-type with no member-types.
    # i.e., It has no effect on a union of types.
    types1.discard(T_TBD)

    if len(types1) == 0:
        # It must be that all types were T_TBD
        return T_TBD
    elif len(types1) == 1:
        return types1.pop()

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
    other_memtypes = []
    for mt in memtypes:
        if mt == T_List or isinstance(mt, ListType):
            list_memtypes.append(mt)
        else:
            other_memtypes.append(mt)

    result_memtypes = union_of_list_memtypes(list_memtypes) + union_of_other_memtypes(other_memtypes)

    assert result_memtypes

    if len(result_memtypes) == 1:
        result = result_memtypes.pop()
    else:
        result = UnionType(result_memtypes)

    # print("union of", ', '.join(str(t) for t in types), " = ", result)

    return result

# ------------------------------------------------------------------------------

def union_of_list_memtypes(list_memtypes):

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

def union_of_other_memtypes(memtypes):

    if len(memtypes) <= 1:
        return memtypes

    tnodes = []
    for mt in memtypes:
        assert isinstance(mt, Type), mt
        assert not isinstance(mt, UnionType), mt
        assert not isinstance(mt, ListType), mt
        tnodes.append(ensure_tnode_for(mt))

    assert tnodes

    for tnode in tnodes:
        tnode._include_all = True

    result_members = []

    def recurse(tnode):
        # Return True iff all of tnode is included in the union.

        if hasattr(tnode, '_include_all'): return True

        if tnode.children:

            children_included = [
                recurse(child)
                for child in tnode.children
            ]

            if False and trace_this_op:
                print(tnode.type, "children_included = ", children_included)

            if all(children_included):
                tnode._include_all = True
                return True
            else:
                for child in tnode.children:
                    if hasattr(child, '_include_all'):
                        result_members.append(child.type)
                return False

        else:
            return False

    if recurse(troot):
        result_members.append(troot.type)

    for tnode in tnodes:
        anc = tnode
        while anc is not None:
            if hasattr(anc, '_include_all'): del anc._include_all
            anc = anc.parent

    return result_members

# ------------------------------------------------------------------------------

#    global compare_types_f
#    compare_types_f = shared.open_for_output('compare_types')
#
#compare_types_memo = {}
#
#def compare_types(A, B):
#    assert isinstance(A, Type)
#    assert isinstance(B, Type)
#
#    # if A == T_TBD: return (T_TBD, B, T_TBD)
#    # assert B != T_TBD
#
#    if (A,B) in compare_types_memo:
#        return compare_types_memo[(A,B)]
#
#    A_memtypes = A.set_of_types()
#    B_memtypes = B.set_of_types()
#
#    # A few cases that can be handled quickly:
#    if A_memtypes == B_memtypes:
#        A_intersect_B = A # or B
#        A_minus_B     = T_0
#        B_minus_A     = T_0
#
#    elif A_memtypes <= B_memtypes:
#        A_intersect_B = A
#        A_minus_B     = T_0
#        B_minus_A     = maybe_UnionType(B_memtypes - A_memtypes)
#
#    elif B_memtypes <= A_memtypes:
#        A_intersect_B = B
#        A_minus_B     = maybe_UnionType(A_memtypes - B_memtypes)
#        B_minus_A     = T_0
#
#    else:
#        # The general case:
#
#        for (nm, t) in [('A', A_memtypes), ('B', B_memtypes)]:
#            attr_name = 'amount_in_' + nm
#
#            for memtype in t:
#                # Treat T_TBD like Top
#                if memtype == T_TBD: memtype = T_Top_ # assert 0
#                start_tnode = ensure_tnode_for(memtype)
#                start_tnode.__setattr__(attr_name, 'all')
#                tnode = start_tnode.parent
#                while tnode is not None:
#                    if hasattr(tnode, attr_name):
#                        assert tnode.__getattribute__(attr_name) == 'some'
#                        break
#                    tnode.__setattr__(attr_name, 'some')
#                    tnode = tnode.parent
#
#        A_minus_B_memtypes = []
#        A_intersect_B_memtypes = []
#        B_minus_A_memtypes = []
#
#        def recurse(tnode, an_ancestor_is_all_in_A=False, an_ancestor_is_all_in_B=False):
#            assert not (an_ancestor_is_all_in_A and an_ancestor_is_all_in_B)
#
#            if an_ancestor_is_all_in_A:
#                amount_of_this_in_A = 'all'
#            elif hasattr(tnode, 'amount_in_A'):
#                amount_of_this_in_A = tnode.amount_in_A
#                del tnode.amount_in_A
#            else:
#                amount_of_this_in_A = 'none'
#
#            if an_ancestor_is_all_in_B:
#                amount_of_this_in_B = 'all'
#            elif hasattr(tnode, 'amount_in_B'):
#                amount_of_this_in_B = tnode.amount_in_B
#                del tnode.amount_in_B
#            else:
#                amount_of_this_in_B = 'none'
#
#            if amount_of_this_in_A == 'all' and amount_of_this_in_B == 'all':
#                A_intersect_B_memtypes.append(tnode.type)
#
#            elif amount_of_this_in_A == 'all':
#                if amount_of_this_in_B == 'some':
#                    for child in tnode.children:
#                        recurse(child, an_ancestor_is_all_in_A=True)
#                elif amount_of_this_in_B == 'none':
#                    A_minus_B_memtypes.append(tnode.type)
#                else:
#                    assert 0 # can't happen
#
#            elif amount_of_this_in_B == 'all':
#                if amount_of_this_in_A == 'some':
#                    for child in tnode.children:
#                        recurse(child, an_ancestor_is_all_in_B=True)
#                elif amount_of_this_in_A == 'none':
#                    B_minus_A_memtypes.append(tnode.type)
#                else:
#                    assert 0 # can't happen
#
#            elif amount_of_this_in_A == 'some' or amount_of_this_in_B == 'some':
#                for child in tnode.children:
#                    recurse(child)
#
#            elif amount_of_this_in_A == 'none' and amount_of_this_in_B == 'none':
#                # (Neither tnode nor any of its subtypes
#                # is in either A_memtypes or B_memtypes.)
#                pass
#
#            else:
#                assert 0 # can't happen
#
#        recurse(troot)
#
#        A_minus_B     = maybe_UnionType(A_minus_B_memtypes)
#        A_intersect_B = maybe_UnionType(A_intersect_B_memtypes)
#        B_minus_A     = maybe_UnionType(B_minus_A_memtypes)
#
#    assert isinstance(A_minus_B,     Type)
#    assert isinstance(A_intersect_B, Type)
#    assert isinstance(B_minus_A,     Type)
#
#    print("%s :: %s  ===>  %s  ///  %s  ///  %s" %
#        (A, B, A_minus_B, A_intersect_B, B_minus_A),
#        file=compare_types_f)
#
#    result = (A_minus_B, A_intersect_B, B_minus_A)
#    compare_types_memo[(A,B)] = result
#    return result

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

class Env:
    def __init__(self):
        self.vars = {}
        self.parameter_names = set()

    def __str__(self):
        return str(self.vars)

    def copy(self):
        e = Env()
        e.vars = self.vars.copy()
        e.parameter_names = self.parameter_names.copy()
        return e

    def equals(self, other):
        return self.vars == other.vars

    def lookup(self, ex):
        return self.vars[ex.source_text()]

    def diff(self, other):
        # Show the difference between two envs. (For debugging.)
        self_keys = set(self.vars.keys())
        other_keys = set(other.vars.keys())

        cats_ = defaultdict(list)

        for key in self.vars.keys() | other.vars.keys():
            if key in self.vars and key in other.vars:
                if self.vars[key] == other.vars[key]:
                    cat = 'entries in both, with same value'
                    line = "`%s`: `%s`" % (key, self.vars[key])
                else:
                    cat = 'entries in both, with different value'
                    line = "`%s`: `%s`  vs  `%s`" % (key, self.vars[key], other.vars[key])
            elif key in self.vars:
                cat = 'entries only in L'
                line = "`%s`: `%s`" % (key, self.vars[key])
            elif key in other.vars:
                cat = 'entries only in R'
                line = "`%s`: `%s`" % (key, other.vars[key])
            else:
                assert 0
            cats_[cat].append(line)

        def show_cat(cat):
            print(cat)
            if cat in cats_:
                for line in cats_[cat]:
                    print("    " + line)
            else:
                print("    (none)")
            print()

        show_cat('entries in both, with same value')
        show_cat('entries in both, with different value')
        show_cat('entries only in L')
        show_cat('entries only in R')

    # ----------------------------------------------------------------

    def plus_new_entry(self, var, t):
        if isinstance(var, str):
            var_name = var
        elif isinstance(var, ANode):
            [var_name] = var.children
        else:
            assert 0

        # assert var_name not in self.vars, var_name
        # disabled assertion dur to _f_ in Number.prototype.toExponential
        if var_name in self.vars:
            add_pass_error(
                var,
                f"plus_new_entry for `{var_name}` when it's already in the env!"
            )

        assert isinstance(t, Type)
        e = self.copy()
        e.vars[var_name] = t
        return e

    def with_var_removed(self, var):
        [var_name] = var.children
        assert var_name in self.vars
        e = self.copy()
        del e.vars[var_name]
        return e

    def augmented_with_return_type(self, return_type):
        e = self.copy()
        e.vars['*return*'] = return_type
        return e

    # ----------------------------------------------------------------

    def assert_expr_is_of_type(self, expr, expected_t):
        assert expected_t != T_TBD

        (expr_t, expr_env) = tc_expr(expr, self)

        if expr_t == T_TBD:
            add_pass_error(
                expr,
                "type of `%s` is TBD, asserted to be of type `%s`"
                % (expr.source_text(), expected_t)
            )
        elif expr_t.is_a_subtype_of_or_equal_to(expected_t):
            pass
        else:
            stderr()
            stderr("assert_expr_is_of_type()")
            stderr("expr      :", expr.source_text())
            stderr("expr_t    :", expr_t)
            stderr("expected_t:", expected_t)
            assert 0
            sys.exit(0)

        return expr_t

    # --------

    def ensure_expr_is_of_type(self, expr, expected_t):
        assert expected_t != T_TBD

        (expr_type, expr_env) = tc_expr(expr, self)

        if expr_type == T_TBD:
            result_env = expr_env.with_expr_type_replaced(expr, expected_t)

        elif expr_type.is_a_subtype_of_or_equal_to(expected_t):
            # great!
            result_env = expr_env

        else:
            expr_text = expr.source_text()
            add_pass_error(
                expr,
                "%s has type %s, but this context expects that it be of type %s"
                % (expr_text, expr_type, expected_t)
            )
            if expr_text == '*null*':
                # Don't try to change the type of *null*!
                result_env = expr_env
            elif expr_text == '&laquo; &raquo;':
                result_env = expr_env
            else:
                result_env = expr_env.with_expr_type_replaced(expr, expected_t)
        return result_env

    def ensure_A_can_be_element_of_list_B(self, item_ex, list_ex):
        (list_type, list_env) = tc_expr(list_ex, self)
        (item_type, item_env) = tc_expr(item_ex, list_env)

        if list_type == T_String and item_type.is_a_subtype_of_or_equal_to(T_String | T_code_unit_):
            # String-contains rather than List-contains
            result = item_env

        elif (list_type == T_List or list_type == ListType(T_TBD)) and item_type == T_TBD:
            # shrug
            result = item_env

        # ----------------------------------------
        # cases where we change the ST of list_ex:

        elif list_type == T_List or list_type == ListType(T_TBD) or list_type == T_TBD:
            result = item_env.with_expr_type_replaced( list_ex, ListType(item_type))

        elif list_type == ListType(T_String) and item_type == T_Symbol:
            result = item_env.with_expr_type_replaced( list_ex, ListType(T_String | T_Symbol))

        elif list_type == ListType(T_PromiseReaction_Record) | T_Undefined and item_type == T_PromiseReaction_Record:
            result = item_env.with_expr_type_narrowed(list_ex, ListType(T_PromiseReaction_Record))

        elif list_type == ListType(T_Match_Record) and item_type == T_Undefined and list_ex.source_text() == '_indices_':
            result = item_env.with_expr_type_replaced(list_ex, ListType(T_Match_Record | T_Undefined))

        # ----------------------------------------
        # cases where we change the ST of item_ex:

        elif item_type == T_TBD:
            result = item_env.with_expr_type_replaced(item_ex, list_type.element_type)

        elif list_type == ListType(T_String) and item_type == T_String | T_Null:
            # ParseModule
            result = item_env.with_expr_type_replaced(item_ex, T_String)

        # ----------------------------------------
        # cases where we don't change either ST:

        elif list_type.is_a_subtype_of_or_equal_to(T_List):
            # use list_type to check type of item_ex
            element_type = list_type.element_type
            result = item_env.ensure_expr_is_of_type(item_ex, element_type)

        else:
            add_pass_error(
                list_ex,
                f"context wants a List type, but got {list_type}"
            )
            result = item_env

        return result

    def with_expr_type_replaced(self, expr, new_t):
        assert isinstance(new_t, Type)
        #
        expr_text = expr.source_text()
        if expr_text in self.vars:
            old_t = self.vars[expr_text]
            assert new_t != old_t

            if (
                old_t == T_TBD and new_t != T_TBD
                or
                old_t == T_not_passed and new_t != T_not_passed
                or
                old_t == T_Top_ and new_t == T_Null | T_String
                # ExportEntriesForModule
                or
                old_t == T_Top_ and new_t == T_Object
                # AtomicLoad
                or
                old_t == T_Top_ and new_t == T_Tangible_
                # GeneratorResumeAbrupt
                or
                old_t == T_List and isinstance(new_t, ListType)
                or
                old_t == T_Tangible_ and new_t in [T_String, T_Boolean, T_Symbol, T_Object] # SameValueNonNumber
                or
                old_t == T_Tangible_ and new_t == T_Number # SameValue, co-ordinated types
                or
                old_t == ListType(T_String) and new_t == ListType(T_String | T_Symbol) # OrdinaryOwnPropertyKeys, maybe others
                #or
                #old_t == T_0 and new_t == T_ResolvedBinding_Record
                ## ResolveExport
                or
                old_t == T_Data_Block | T_Shared_Data_Block and new_t == T_Shared_Data_Block and expr_text == '_toBlock_' # CopyDataBlockBytes, because I can't handle co-ordinated types
                or
                old_t == T_Data_Block | T_Shared_Data_Block | T_Null and (
                    new_t == T_Shared_Data_Block
                        # GetModifySetValueInBuffer, because I can't represent the effect of IsSharedArrayBuffer
                    or
                    new_t == T_Data_Block
                        # SetValueInBuffer, ditto
                )
                or
                old_t == T_Number and new_t == T_MathInteger_
                    # e.g. ReadModifyWriteSharedMemory{ ... [[ElementSize]]: _elementSize_. ...}
                    # in GetModifySetValueInBuffer
                or
                old_t == ListType(T_PTN_ForBinding) and old_t.is_a_subtype_of_or_equal_to(new_t) # VarScopedDeclarations
                or
                old_t == T_Boolean | T_not_set and new_t == T_Boolean
                # ContainsDuplicateLabels, because of re-use of _hasDuplicates_
                or
                old_t == ListType(ListType(T_code_unit_) | T_String) and new_t == ListType(T_String)
                # TemplateStrings
                or
                old_t == T_Tangible_ | T_not_set and new_t == T_Tangible_
                # CaseBlockEvaluation, will go away with refactoring
                or
                old_t == T_empty_ and new_t == ptn_type_for('MethodDefinition')
                # ClassDefinitionEvaluation
                or
                old_t == T_Normal and new_t == T_methodDef_record_
                # ClassDefinitionEvaluation
                or
                old_t == T_Property_Descriptor | T_Undefined and new_t == T_Property_Descriptor
                # CreateGlobalFunctionBinding
                or
                old_t == ptn_type_for('AssignmentPattern') | T_not_set and new_t == T_Parse_Node
                # ForIn/OfBodyEvaluation
                or
                old_t == T_Boolean | T_Environment_Record | T_Number | T_Object | T_String | T_Symbol | T_Undefined and new_t == T_Object
                # GetValue. (Fix by replacing T_Reference_Record with ReferenceType(base_type)?)
                or
                old_t == T_Abrupt | T_Boolean | T_Intangible_ | T_Null | T_Number | T_Object | T_String | T_Symbol and new_t == T_Environment_Record
                # InitializeBoundName
                or
                old_t == T_Normal and new_t == T_Tangible_
                # PropertyDefinitionEvaluation
                or
                old_t == ListType(T_TBD) and new_t == ListType(T_Tangible_)
                # ArgumentListEvaluation
                or
                old_t | T_Abrupt == new_t
                or
                old_t | T_throw_ == new_t
                or
                old_t == T_Tangible_ | T_empty_ and new_t == ListType(T_code_unit_) | T_String
                # Evaluation for TemplateLiteral
                or
                expr_text in ['_test_', '_increment_'] and new_t == T_Parse_Node
                or
                old_t == T_Environment_Record | T_Undefined and new_t == T_Environment_Record
                # IteratorBindingInitialization
                or
                old_t == T_String | T_Symbol | T_Undefined and new_t == T_String | T_Symbol
                # ValidateAndApplyPropertyDescriptor
                or
                old_t == ListType(T_code_unit_) and new_t == T_String
                # TemplateStrings
                or
                old_t == T_Tangible_ and new_t == T_function_object_
                # [[Construct]]
                or
                old_t == T_Null | T_Object and new_t == T_Object
                # [[Construct]]
                or
                old_t == T_Tangible_ | T_empty_ and new_t == T_Tangible_
                # ??
                or
                old_t == T_Tangible_ | T_empty_ and new_t == ListType(T_code_unit_) | T_String | T_code_unit_
                or old_t == ListType(T_code_unit_) | T_Reference_Record | T_Tangible_ | T_empty_ and new_t == ListType(T_code_unit_) | T_String | T_code_unit_
                # Evaluation of TemplateLiteral : TemplateHead Expression TemplateSpans
                or
                old_t == ListType(T_code_unit_) | T_Reference_Record | T_Tangible_ | T_empty_ and new_t == ListType(T_code_unit_) | T_String
                # Evaluation of TemplateMiddleList : TemplateMiddleList TemplateMiddle Expression
                or
                old_t == T_Tangible_ | T_empty_ and new_t == T_String | T_Symbol
                # DefineMethod
                or
                old_t == ListType(T_code_unit_) | T_Reference_Record | T_Tangible_ | T_empty_ and new_t == T_String | T_Symbol
                # DefineMethod
                or
                old_t == T_MathInteger_ | T_Tangible_ | T_code_unit_ and new_t == T_MathInteger_ | T_Number | T_code_unit_
                # [[DefineOwnProperty]]
                or
                old_t == T_Tangible_ | T_code_unit_ and new_t == T_Number | T_code_unit_
                or
                old_t == T_String | T_Undefined and new_t == T_String
                # GeneratorResume
                or
                old_t == T_CharSet | ThrowType(T_SyntaxError) and new_t == T_CharSet
                or
                old_t == ListType(T_Tangible_) and new_t == ListType(T_String)
                # InternalizeJSONProperty
                or
                old_t == T_Abrupt | T_Boolean | T_Intangible_ | T_Null | T_Number | T_Object | T_String | T_Symbol and new_t == ListType(T_code_unit_) | T_String | T_code_unit_
                # SerializeJSONObject
                or
                old_t == ListType(T_code_unit_) | T_Undefined | T_code_unit_ and new_t == ListType(T_code_unit_)
                # TemplateStrings
                or
                old_t == ListType(T_code_unit_) | T_Undefined | T_code_unit_ and new_t == ListType(T_code_unit_) | T_String | T_code_unit_
                # Evaluation of SubstitutionTemplate
                or
                old_t == ListType(T_code_unit_) | T_Undefined | T_code_unit_ and new_t == ListType(T_code_unit_) | T_String
                # Evaluation of TemplateMiddleList
                or
                old_t == T_Abrupt | T_Tangible_ | T_empty_ and new_t == T_Abrupt | T_Tangible_
                # AsyncGeneratorResumeNext
                or
                old_t == T_Undefined and new_t == T_Object #???
                # Evaluation (YieldExpression)

            ):
                pass
            else:
                stderr()
                stderr("with_expr_type_replaced")
                stderr("expr :", expr_text)
                stderr("old_t:", old_t)
                stderr("new_t:", new_t)
                # assert 0
                # sys.exit(0)
        else:
            # expr_text not in self.vars
            assert expr_text in [
                '! UTF16EncodeCodePoint(_cp_)',
                '? CaseClauseIsSelected(_C_, _input_)', # Evaluation (CaseBlock)
                '? Get(_obj_, `"length"`)',
                '? GetValue(_defaultValue_)', # DestructuringAssignmentEvaluation, bleah
                '? InnerModuleEvaluation(_requiredModule_, _stack_, _index_)', # InnerModuleEvaluation
                '? InnerModuleLinking(_requiredModule_, _stack_, _index_)', # InnerModuleLinking
                '? IteratorValue(_innerResult_)', # Evaluation of YieldExpression
                '? IteratorValue(_innerReturnResult_)', # Evaluation of YieldExpression
                '? ToPrimitive(_x_)', # Abstract Equality Comparison
                '? ToPrimitive(_y_)', # Abstract Equality Comparison
                '? ToPropertyKey(_lval_)',
                'Call(_return_, _iterator_)', # AsyncIteratorClose
                'UTF16EncodeCodePoint(_V_)',
                'StringValue of |Identifier|',
                'ToInteger(_P_)', # [[OwnPropertyKeys]]
                'ToNumber(_x_)', # Abstract Equality Comparison
                'ToNumber(_y_)', # Abstract Equality Comparison
                'ToPrimitive(_x_)',
                'ToPrimitive(_y_)',
                'ToPropertyKey(_lval_)',
                '_cookedStrings_[_index_]', # because of TemplateStrings return type
                '_e_.[[LocalName]]', # ResolveExport
                '_ee_.[[LocalName]]',
                '_module_.[[DFSAncestorIndex]]', # InnerModuleEvaluation
                '_module_.[[DFSIndex]]', # InnerModuleEvaluation
                '_rawStrings_[_index_]', # ResolveExport
                '_requiredModule_.[[DFSAncestorIndex]]', # InnerModuleEvaluation
                '_scriptRecord_.[[Realm]]',
                '_throwawayCapability_.[[Promise]]', # AsyncFunctionAwait
                'the MV of |DecimalDigits|',
                'the MV of the first |DecimalDigits|',
                'the MV of |StrUnsignedDecimalLiteral|',
                'the TV of |TemplateCharacter|',
                'the TV of |TemplateCharacters|',
                'the TV of |NoSubstitutionTemplate|',
                'the VarDeclaredNames of |Statement|',
                'the VarScopedDeclarations of |Statement|',
                'the result of performing ArrayAccumulation of |ElementList| with arguments _array_ and _nextIndex_',
                'the result of performing ArrayAccumulation of |Elision| with arguments _array_ and _nextIndex_',
                'the result of performing IteratorDestructuringAssignmentEvaluation of |AssignmentRestElement| with _iteratorRecord_ as the argument',
                'the result of performing IteratorDestructuringAssignmentEvaluation of |Elision| with _iteratorRecord_ as the argument', # hm
                '(16 times the MV of the first |HexDigit|) plus the MV of the second |HexDigit|',
                '(0x1000 times the MV of the first |HexDigit|) plus (0x100 times the MV of the second |HexDigit|) plus (0x10 times the MV of the third |HexDigit|) plus the MV of the fourth |HexDigit|',
                '_f_ + 1', # Number.prototype.toExponential
                '_f_ + 1 - _k_', # Number.prototype.toFixed
                '_k_ - _f_', # toFixed
                '_p_ - 1', # toPrecision
                '_p_ - (_e_ + 1)', # toPrecision
                '_srcBuffer_.[[ArrayBufferData]]', # %TypedArray%.prototype.set
                '_targetBuffer_.[[ArrayBufferData]]', # %TypedArray%.prototype.set
                'the result of performing NamedEvaluation of |Initializer| with argument _bindingId_',
                '_handler_', # NewPromiseReactionJob
                '_r_.[[Value]]',
                '%Generator.prototype.next%', # CreateListIteratorRecord
                '%GeneratorFunction.prototype.prototype.next%',
                '? Yield(IteratorValue(_innerResult_))', # Evaluation
                '? Yield(IteratorValue(_innerReturnResult_))', # Evaluation
                '_list_[_index_]', # CreateListIteratorRecord
                '\u211d(_tv_)', # TimeString
                'abs(_offset_)', # TimeZoneString
                '1<sub>\U0001d53d</sub>', # MakeDay
                '\u211d(_m_)', # MakeDay
                'WeekDay(_tv_)', # Date.prototype.toUTCString
                'MonthFromTime(_tv_)',
                'abs(\u211d(_yv_))',
                '\u211d(_n_)', # unescape
                '\u211d(_lastIndex_)', # RegExpBuiltinExec
                '\u211d(_ny_)', # Math.atan2
                '\u211d(_nx_)', # Math.atan2
                '\u211d(_exponent_)', # Number::exponentiate
                '\u211d(_d_)', # Number::remainder
                'the StringValue of |IdentifierName|', # StringValue
                'PropName of |FieldDefinition|', # Early Errors
                '_generator_.[[AsyncGeneratorState]]', # AsyncGeneratorResume
                '_m_.[[CycleRoot]]', # GatherAsyncParentCompletions
                '_promiseCapability_.[[Reject]]', # CallDynamicImportFulfilled
                '_promiseCapability_.[[Resolve]]', # CallDynamicImportFulfilled
                '\u211d(_t_ / msPerDay)', # Day
                '\u211d(_t_ / msPerHour)', # HourFromTime
                '\u211d(_t_ / msPerMinute)', # MinFromTime
                '\u211d(_t_ / msPerSecond)', # SecFromTime
                'ReferencedBindings of |NamedExports|',
                'PrototypePropertyNameList of |ClassElementList|',
                '_lref_.[[ReferencedName]]',
            ], expr_text.encode('unicode_escape')
        #
        e = self.copy()
        e.vars[expr_text] = new_t
        return e

    def set_A_to_B(self, settable, expr):
        (settable_type, env1) = tc_expr(settable, self)
        (expr_type,     env2) = tc_expr(expr,     env1)

        if settable.source_text() in self.parameter_names:
            add_pass_error(
                settable,
                "Error: setting a parameter"
            )

        if settable_type == T_TBD and expr_type == T_TBD:
            return env2

        elif settable_type == T_TBD:
            # flow type info from expr to settable
            return self.with_expr_type_replaced(settable, expr_type)

        elif expr_type == T_TBD:
            # flow type info from settable to expr
            # this is questionable
            return self.with_expr_type_replaced(expr, settable_type)

        elif expr_type == settable_type:
            return env2

        elif expr_type == T_List and isinstance(settable_type, ListType):
            # E.g., expr is an empty List constructor
            # XXX Still need this?
            return env2

        else:
            # ??:
            # settable_type is mostly irrelevant,
            # unless we distinguish the type that a settable is *allowed* to have,
            # versus the type that it happens to have right now.
            #
            # parameters:
            #     - _iSL_ (optional) List of SlotName_
            #   1.If _iSL_ was not provided, set _iSL_ to a new empty List
            # Setting _iSL_ does change the type that it has after that command,
            # but it shouldn't change the declared type of the parameter.
            # But we use exit envs to infer changes to the parameter types.
            # (which makes sense when their declared type is TBD, or maybe just 'List',
            # but not so much otherwise.

            # XXX If the settable is a DOTTING, we should disallow
            # an expr_t that is outside the allowed type of the dotting

            settable_text = settable.source_text()
            if expr_type.is_a_subtype_of_or_equal_to(settable_type):
                # A change, but probably not worth mentioning
                pass
            elif settable_type == T_not_passed:
                # "If _foo_ was not passed, set _foo_ to X."
                # Not worth warning about type-change.
                pass
            else:
                add_pass_error(
                    settable,
                    "warning: Set `%s` changes type from `%s` to `%s`" %
                    (settable_text, settable_type, expr_type)
                )
            e = env2.copy()
            e.vars[settable_text] = expr_type
            return e

    # ----------------------------------------------------------------

    def with_expr_type_narrowed(self, expr, narrower_t):
        assert isinstance(narrower_t, Type)
        (expr_t, env1) = tc_expr(expr, self)

        # super-kludge:
        if expr.source_text() in ['_highest_', '_lowest_'] and expr_t == T_InfiniteNumber_:
            # Math.max, Math.min
            expr_t = T_Number

        if expr_t.is_a_subtype_of_or_equal_to(narrower_t):
            # expr is already narrower than required.
            return env1

        # Treat T_TBD like Top:
        if expr_t == T_TBD:
            pass
        elif narrower_t.is_a_subtype_of_or_equal_to(expr_t):
            pass
        else:
            stderr("expr %r of type %s cannot be narrowed to %s" % (expr.source_text(), expr_t, narrower_t))
            assert 0
        #
        expr_text = expr.source_text()
        e = env1.copy()
        e.vars[expr_text] = narrower_t
        return e

    # ----------------------------------------------------------------

    def with_type_test(self, expr, copula, target_t, asserting):
        # Returns a pair of Envs:
        # one in which the the type-test is true, and one in which it's false.
        # i.e.,
        # - one in which the expr's current type is narrowed to be <: target_t; and
        # - one in which its type is narrowed to have no intersection with target_t
        # (either respectively or anti-respectively, depending on copula.)

        expr_text = expr.source_text()

        (expr_t, env1) = tc_expr(expr, self)

        if spec.text[expr.start_posn-5:expr.start_posn] == 'Type(' and not expr_t.is_a_subtype_of_or_equal_to(T_Tangible_):
            add_pass_error(
                expr,
                f"ST of Type() arg is {expr_t}"
            )

        # assert env1 is self
        # No, e.g. expr_text is '_R_.[[Value]]', where the out-env
        # has a narrower binding for _R_.

        assert target_t != T_TBD

        if asserting and expr_t == T_TBD:
            if copula == 'is a':
                true_env = env1.copy()
                true_env.vars[expr_text] = target_t
                false_env = None
                return (true_env, false_env)
            else:
                # XXX wah
                return (env1, env1)

            # pdb.set_trace()

        (part_inside_target_t, part_outside_target_t) = expr_t.split_by(target_t)

        assert isinstance(part_outside_target_t, Type)
        assert isinstance(part_inside_target_t, Type)

        if asserting:
            if copula == 'is a':
                # We are asserting that the value of `expr` is of the target type.
                # So it'd be nice if the static type of `expr` were a subtype of the target type.
                if part_inside_target_t == T_0:
                    add_pass_error(
                        expr,
                        "ST of `%s` is `%s`, so can't be a `%s`"
                        % (expr_text, expr_t, target_t)
                    )

                if part_outside_target_t != T_0:
                    add_pass_error(
                        expr,
                        "STA fails to confirm that %s is a %s; could also be %s" %
                        (expr_text, target_t, part_outside_target_t)
                    )
                    # e.g. a parameter type starts as TBD.
                    # but because the Assert will only propagate the 'true' env,
                    # this error will probably disappear in a later pass.


            elif copula == 'isnt a':
                # We expect that the static type of the expr has no intersection with the target type.

                if part_inside_target_t != T_0:
                    add_pass_error(
                        expr,
                        "ST of `%s` is `%s`, so can't confirm the assertion -- value might be `%s`"
                        % (expr_text, expr_t, part_inside_target_t)
                    )
                assert part_outside_target_t != T_0
            else:
                assert 0, copula
        else:
            # Outside of an assertion,
            # you're presumably doing the type-test
            # with the expectation that either outcome is possible.
            if part_outside_target_t == T_0:
                add_pass_error(
                    expr,
                    # XXX "static type is X, so must be Y"
                    "STA indicates that it's unnecessary to test whether `%s` is %s, because it must be" % (
                        expr_text, target_t)
                )
                # ResolveExport _starResolution_ loop thing

            if part_inside_target_t == T_0:
                add_pass_error(
                    expr,
                    # XXX "static type is X, so can't be Y"
                    "STA indicates that it's unnecessary to test whether `%s` is %s, because it can't be" % (
                        expr_text, target_t)
                )
                # Perhaps a parameter-type was too restrictive.

        intersect_env = env1.copy()
        nointersect_env = env1.copy()
        intersect_env.vars[expr_text] = part_inside_target_t
        nointersect_env.vars[expr_text] = part_outside_target_t

        if copula == 'is a':
            return (intersect_env, nointersect_env)
        else:
            return (nointersect_env, intersect_env)

    def reduce(self, header_names):
        e = Env()
        for (vn, vt) in self.vars.items():
            if vn in header_names:
                e.vars[vn] = vt

        e.parameter_names = self.parameter_names
        return e

# ------------------------------------------------------------------------------

def env_and(env1, env2):
    # Return an Env that expresses that both env1 and env2 hold.
    return envs_and([env1, env2])

def envs_and(envs):
    if len(envs) == 0: assert 0
    if len(envs) == 1: return envs[0]

    # optimization:
    if len(envs) == 2 and envs[0].vars == envs[1].vars: return envs[0]

    e = Env()
    vars = set.intersection(*[ set(env.vars.keys()) for env in envs ])
    for expr_text in vars:
        ts = [ env.vars[expr_text] for env in envs ]
        ts = [ t for t in ts if t != T_TBD ]
        if ts == []:
            intersection_t = T_TBD
        else:
            intersection_t = ts[0]
            for t in ts[1:]:
                (intersection_t, _) = intersection_t.split_by(t)
        e.vars[expr_text] = intersection_t
    return e

def env_or(env1, env2):
    # Return an Env that expresses that either env1 or env2 (or both) hold.
    return envs_or([env1, env2])

def envs_or(envs):
    envs = [env for env in envs if env is not None]
    if len(envs) == 0: return None
    if len(envs) == 1: return envs[0]

    e = Env()

    all_vars = set()
    for env in envs:
        for var_name in env.vars.keys():
            all_vars.add(var_name)

    for var_name in sorted(all_vars):
        e.vars[var_name] = union_of_types([
            env.vars[var_name] if var_name in env.vars else T_not_set
            for env in envs
        ])

    all_param_names = set()
    for env in envs:
        all_param_names.update(env.parameter_names)
    e.parameter_names = all_param_names

    return e

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def do_static_type_analysis(levels):

    atexit.register(write_modified_spec)
    # This was useful when I was gradually building up the set of STA rules,
    # because even if the STA-run ended in an exception (which was usual),
    # I would still get a spec_w_errors written, which might show a little more progress.
    # Now, if STA ends in an exception, spec_w_errors would probably be of no use.

    global split_types_f
    split_types_f = shared.open_for_output('split_types')

    global sta_misc_f
    sta_misc_f = shared.open_for_output('sta_misc')

    global g_level_prefix
    for (L, clusters_on_level_L) in enumerate(levels):
        print()
        print("X" * 60)
        print("X" * 60)
        print("level", L)
        time.sleep(1)
        g_level_prefix = '[%d] ' % L
        n_clusters_this_level = len(clusters_on_level_L)
        for (c, cluster) in enumerate(clusters_on_level_L):
            print()
            print("X" * 50)
            print("level %d, cluster %d/%d (%d ops):" %
                (L, c, n_clusters_this_level, len(cluster.members))
            )
            print()

            pass_num = 0
            while True:
                pass_num += 1
                print()
                print("=" * 40)
                print("level %d : cluster %d/%d : pass #%d..."
                    % (L, c, n_clusters_this_level, pass_num))
                if pass_num == 6:
                    print("giving up")
                    sys.exit(1)
                global pass_errors
                pass_errors = []
                n_ops_changed = 0
                for alg in cluster.members:
                    changed = tc_alg(alg)
                    if changed: n_ops_changed += 1
                print("%d operations changed" % n_ops_changed)
                if n_ops_changed > 0:
                    # The cluster's static types haven't settled yet.
                    if pass_errors:
                        print("discarding %d errors" % len(pass_errors))
                else:
                    # The cluster's static types have hit a fixed point.
                    print("achieved fixed point after %d passes" % pass_num)
                    if pass_errors:
                        print("accepting %d errors" % len(pass_errors))
                        for (anode, msg) in pass_errors:
                            install_error(anode, msg)
                    break

        # if L == 1: break

    print()
    print("Finished static analysis!")
    print()

    write_modified_spec(mode = 'messages in algs and dls')
    write_modified_spec(mode = 'dls w revised info')

    # Type-check loops better.

    # Drop the warning for when 'Set' changes the type?

    # For operations with multiple defns (SDOs and CMs),
    # need to remember the return type of each individual defn,
    # then use knowledge of the type of the 'thing'
    # to get the set of defns that might be invoked,
    # and thus a narrower result type than currently.

    # So need to know the grammar.
    # (a) to find that set of defns (note chain rules), and
    # (b) to check {PROD_REF}s like "the second |Expression|".

    # Get rid of Normal?
    # Get rid of Intangible?
    # Introduce Present/Absent dichotomy?
    # Introduce more subtypes?

    # Algorithms for built-ins?

    # Distinguish the declared type (or maximum type) of a variable
    # versus its current type.

# ------------------------------------------------------------------------------

g_level_prefix = '[-] '
pass_errors = []

def add_pass_error(anode, msg):
    global pass_errors
    assert isinstance(anode, ANode)
    print("??:", msg.encode('unicode_escape'))
    pass_errors.append((anode, g_level_prefix + msg))

def install_error(anode, msg):
    if not hasattr(anode, 'parent'):
        # It's a fake node.
        # Just attach the msg to the node.
        if not hasattr(anode, 'errors'):
            anode.errors = []
        anode.errors.append(msg)
    else:
        # It's a real node.
        shared.put_targeted_msg(anode, msg)

# ------------------------------------------------------------------------------

def write_modified_spec(mode = 'messages in algs and dls'):
    assert mode in ['messages in algs and dls', 'dls w revised info']

    show_targeted_msgs = (mode == 'messages in algs and dls')

    if mode == 'messages in algs and dls':
        filename = 'spec_w_errors'
    else:
        filename = 'spec_w_edits'
    stderr(f"printing {filename} ...")

    f = shared.open_for_output(filename)

    shared.write_spec_with_extras(mode, show_targeted_msgs, f)

    f.close()

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def mytrace(env):
    if env is None:
        print("resulting env is None")
    else:
        # print("resulting env:", env)
        for var_name in ['_number_']:
            print("---> %s : %s" % (var_name, env.vars.get(var_name, "(not set)")))
            # assert 'LhsKind' not in str(env.vars.get(var_name, "(not set)"))

def tc_alg(alg):
    print()
    print('-' * 30)
    print(alg)

    # if alg.name == '[[Call]]': pdb.set_trace()

    if alg.name in built_in_ops:
        print('skipping built-in')
        return False # no change

    global trace_this_op
    trace_this_op = False
    trace_this_op = (alg.name in [
        'xToIntegerOrInfinity'
    ])
    # and you may want to tweak mytrace just above

    any_change = False
    for header in alg.headers:
        c = tc_header(header.tah)
        if c: any_change = True

    if any_change:
        summarize_headers(alg)

    if trace_this_op:
        pass
        # need to do this if tracing doesn't cause pause
        pdb.set_trace()
        # stderr("ABORTING BECAUSE trace_this_op IS SET.")
        # sys.exit(1)

    return any_change

# --------------------------------

def tc_header(tah):

    init_env = tah.make_env()

    if tah.t_defns == []:
        return False

    # Eventually, `tah` will also contain (ahead of time)
    # an indication of the operation's expected return type.
    # We should complain about any return-points
    # that do not conform.
    # In the meantime, ...
    if tah.species.startswith('bif:'):
        expected_return_type = T_Tangible_ | T_throw_ | T_empty_
        # T_empty_ shouldn't really be allowed,
        # but if I leave it out,
        # I get a bunch of complaints that I think are false positives.
    else:
        expected_return_type = T_Top_

    final_env = tc_proc(tah.name, tah.t_defns, init_env, expected_return_type)

    if tah.name == 'Early Errors':
        assert final_env is None
        return False

    assert final_env is not None

    for (pn, final_t) in final_env.vars.items():
        if final_t == T_TBD:
            add_pass_error(
                tah.fake_node_for_[pn],
                "after STA, the type of `%s` is still TBD" % pn
            )

    if init_env.vars == final_env.vars:
        # no change
        return False
    else:
        # Something is different between init_env and final_env,
        # but that doesn't necessarily mean that we're going to change header types
        changed_op_info = False
        for pn in sorted(init_env.vars.keys()):
            init_t = init_env.vars[pn]
            final_t = final_env.vars[pn]

            # if final_t == T_Top_: final_t = T_TBD

            # if init_t == T_TBD and final_t == T_TBD:
            #     add_pass_error(
            #         tah.fake_node_for_[pn],
            #         'param %r is still TBD' % (pn,)
            #     )

            # if isinstance(final_t, UnionType) and len(final_t.member_types) >= 12:
            #     print("%s : %s : # member_types = %d" % (tah.name, pn, len(final_t.member_types)))

            if init_t == final_t: continue

            # if tah.name == 'RequireInternalSlot': pdb.set_trace()
            if (
                # cases in which we don't want to change header types:
                init_t == ListType(T_code_unit_) and final_t == T_code_unit_ | ListType(T_code_unit_)
                or
                final_t not in [T_TBD, T_0] and init_t == final_t | T_not_passed
                # ObjectCreate's _internalSlotsList_
                # Call's _argumentsList_
                or
                init_t == T_String | T_Symbol and final_t == T_String
                # SetFunctionName
                or
                init_t == T_Abrupt | T_Tangible_ | T_empty_ and final_t == ListType(T_code_unit_) | T_Top_
                # Evaluation
                or
                tah.name == 'SetRealmGlobalObject' and pn == '_thisValue_' and init_t == T_Tangible_
                or
                tah.name == 'SetRealmGlobalObject' and pn == '_globalObj_' and init_t == T_Object | T_Undefined
                or
                tah.name == 'UTF16EncodeCodePoint' and pn == '*return*' and init_t == ListType(T_code_unit_)
                or
                tah.name == 'PerformPromiseThen' and pn in ['_onFulfilled_', '_onRejected_'] and init_t == T_Tangible_
                or
                tah.name == 'TemplateStrings' and pn == '*return*' and init_t == ListType(T_String)
                or
                tah.name == 'Construct' and pn == '_newTarget_' and init_t == T_Tangible_ | T_not_passed
                or
                tah.name == 'OrdinaryHasInstance' and pn == '_O_'
                or
                tah.name == 'GetIterator' and pn == '_method_'
                or
                tah.name == 'ResolveBinding' and pn == '_env_'
                or
                tah.name == 'ToLength' and pn == '*return*' and init_t == T_IntegralNumber_ | ThrowType(T_TypeError)
                # STA isn't smart enough to detect that the normal return is always integer,
                # wants to change it to Number
                or
                tah.name == 'PerformPromiseThen' and pn == '_resultCapability_'
                # STA wants to add T_Undefined, which is in the body type, but not the param type
                or
                tah.name == 'FlattenIntoArray' and pn == '*return*' and init_t == T_MathInteger_ | T_throw_ and final_t == T_throw_
                # not sure why STA isn't picking up Integer
                or
                tah.name == 'SetFunctionName' and pn == '_name_' and init_t == T_Private_Name | T_String | T_Symbol and final_t == T_String
                or
                (
                    # This is a somewhat hacky way to prevent 'throw_' being widened to 'Abrupt'
                    # in the return type of various evaluation-relevant SDOs.
                    tah.name in [
                        'BindingClassDeclarationEvaluation',
                        'ClassDefinitionEvaluation',
                        'ClassElementEvaluation',
                        'ClassFieldDefinitionEvaluation',
                        'DefineMethod',
                        'NamedEvaluation',
                        'PropertyDefinitionEvaluation',
                    ]
                    and
                    pn == '*return*'
                    and
                    T_throw_.is_a_subtype_of_or_equal_to(init_t)
                    and
                    not T_continue_.is_a_subtype_of_or_equal_to(init_t)
                    and
                    T_continue_.is_a_subtype_of_or_equal_to(final_t)
                )
                or
                tah.name == 'MakeConstructor' and pn == '_F_' and init_t == T_function_object_
                or
                tah.name == 'String.prototype.localeCompare' and pn == '*return*'
                # The algo is incomplete, so doesn't result in a reasonable return type.
                or
                tah.name == '[[Call]]' and pn == '*return*'
                or
                tah.name == '[[Construct]]' and pn == '*return*'
                or
                tah.name == 'StringToCodePoints' and pn == '*return*'
                or
                tah.name == 'UTF16EncodeCodePoint' and pn == '_cp_'
                or
                tah.name == 'UTF16Encoding' and pn == '_cp_'
                or
                tah.name == 'BigIntBitwiseOp' and pn in ['_x_', '_y_']
                # algo just overwrites them with different types
                or
                tah.name == 'LocalTime' and pn == '*return*' and init_t == T_MathInteger_ and  final_t == T_Number
                # mess
                or
                tah.name == 'ToInteger'
                or
                tah.name == 'Math.fround' and pn == '_x_'
                or
                tah.name == 'Number.isFinite' and pn == '_number_'
                or
                tah.name == 'IsIntegralNumber' and pn == '_argument_'
                or
                tah.name == 'AdvanceStringIndex' and pn == '_index_'
                or
                tah.name == 'ArrayAccumulation' and pn == '_nextIndex_'
                or
                tah.name == 'BigInt.asIntN' and pn == '_bits_'
                or
                tah.name == 'BigInt.asUintN' and pn == '_bits_'
                or
                tah.name == 'CreateBuiltinFunction' and pn == '_realm_'
                or
                tah.name == 'ClassElementEvaluation' and pn == '*return*'
                or
                tah.name == 'CompilePattern' and pn == '*return*'
                or
                tah.name == 'GeneratorYield' and pn == '*return*'
                or
                tah.name == 'Evaluation' and pn == '*return*'
                or
                tah.name == 'GeneratorValidate' and pn == '*return*'
                or
                tah.name == 'ProxyCreate' and pn == '*return*'
                or
                tah.name == 'CreateMapIterator' and pn == '*return*'
                or
                tah.name == 'CreateSetIterator' and pn == '*return*'
                or
                tah.name == 'TypedArrayCreate' and pn == '*return*' # should handle ValidateTypedArray() as a type-check
                or
                tah.name == 'EvaluateGeneratorBody' and pn == '*return*'
                or
                tah.name == 'EvaluateAsyncGeneratorBody' and pn == '*return*'
                or
                tah.name == 'SetRealmGlobalObject' and pn == '_thisValue_'
                or
                tah.name == 'DetachArrayBuffer' and pn == '_key_'
            ):
                # -------------------------
                # Don't change header types
                continue

            elif (
                # cases in which we *do* want to change header types:
                # ----
                init_t == T_TBD
                or
                init_t == T_TBD | T_not_passed
                or
                init_t == ListType(T_TBD)
                or
                init_t == T_List and isinstance(final_t, ListType)
                # ----
                or
                init_t.is_a_subtype_of_or_equal_to(final_t)
                # This pass just widened the type.
                # [Maybe this is too general.]
                # ------
                or
                final_t.is_a_subtype_of_or_equal_to(init_t) and (
                    tah.name == 'InstantiateFunctionObject'
                    or
                    tah.name == 'GetThisBinding' and init_t == T_Tangible_ | ThrowType(T_ReferenceError)
                    or
                    tah.name == 'WithBaseObject' and init_t == T_Object | T_Undefined
                    or
                    tah.name == 'SameValueNonNumeric' and init_t == T_Tangible_
                    or
                    tah.name.endswith('DeclarationInstantiation') and pn == '_env_' and init_t == T_Environment_Record
                    or
                    tah.name == 'AsyncGeneratorResume' and pn == '_completion_'
                    or
                    tah.name == 'AsyncGeneratorCompleteStep' and pn == '_completion_'
                    or
                    tah.name == 'CallDynamicImportFulfilled' and pn == '_result_' and init_t == T_Tangible_ and final_t == T_Undefined
                    or
                    pn == '*return*' # too general?
                )
                # This pass just narrowed the type.
                # ----
                or
                init_t == T_Tangible_ and tah.name == 'SameValueNonNumber'
                or
                init_t == T_Tangible_ and final_t == T_Object | T_Undefined and tah.name == 'PrepareForOrdinaryCall'
                # eoh is just wrong
                or
                init_t == T_Tangible_ and final_t == T_Null | T_Object and tah.name == 'OrdinarySetPrototypeOf'
                # eoh is just wrong
                or
                init_t == T_Normal and final_t == T_function_object_
                or
                tah.name == 'MakeConstructor' and init_t == T_function_object_ and final_t == T_constructor_object_
                or
                tah.name == 'SetFunctionLength' and pn == '_length_' and init_t == T_Number and final_t == T_MathInteger_
                or
                tah.name == 'CodePointsToString' and pn == '_text_' and init_t == T_Unicode_code_points_ and final_t == ListType(T_code_point_)

                # eoh is just wrong, because preamble is misleading
                or
                tah.name == 'ObjectDefineProperties' and pn == '_O_'
                or
                tah.name == 'TimeString' and pn == '_tv_'
                or
                tah.name == 'DateString' and pn == '_tv_'
                or
                tah.name == 'SerializeJSONArray' and pn == '_value_'
                or
                tah.name == 'NormalCompletion' and pn == '_value_' and init_t == T_Tangible_ | T_Intangible_ and final_t == T_Tangible_ | T_empty_ # TODO

                # or
                # tah.name == 'CreatePerIterationEnvironment' and init_t == T_Undefined | T_throw_ and final_t == T_Undefined | ThrowType(T_ReferenceError)
                # # cheater artifact
                # or
                # tah.name == 'InitializeReferencedBinding' and init_t == T_Boolean | T_empty_ | T_throw_ and final_t == T_empty_ | T_throw_
                # # cheater artifact
                # or
                # tah.name == 'PutValue' and init_t == T_Boolean | T_Undefined | T_empty_ | T_throw_ and final_t == T_Boolean | T_Undefined | T_throw_
                # # cheater artifact
                # or
                # tah.name == 'InitializeBoundName' and init_t == T_Boolean | T_Undefined | T_empty_ | T_throw_ and final_t == T_Boolean | T_Undefined | T_throw_
            ):
                # fall through to change the header types
                pass
            else:
                assert 0, (tah.name, pn, str(init_t), str(final_t))
                # We should deal with this case above.

            if trace_this_op:
                print(f"About to change the declared_type of {pn} to {final_t}")
                input('hit return to continue ')

            tah.change_declared_type(pn, final_t)

            changed_op_info = True

        return changed_op_info

# ------------------------------------------------------------------------------

proc_return_envs_stack = []

def tc_proc(op_name, defns, init_env, expected_return_type=T_Top_):
    assert defns

    header_names = sorted(init_env.vars.keys())

    proc_return_envs_stack.append(set())

    global proc_expected_return_type
    proc_expected_return_type = expected_return_type

    for (i, (discriminator, body)) in enumerate(defns):
        if op_name is not None:
            print()
            print('-' * 20)
            print("%s : defn #%d/%d:" % (op_name, i+1, len(defns)))

        # global trace_this_op
        # trace_this_op = (op_name == 'SV' and i == 27)

        if discriminator:
            if isinstance(discriminator, Type):
                print(discriminator)
            elif hasattr(discriminator, 'source_text'):
                print(discriminator.source_text())
            else:
                assert 0
        else:
            print('(no discriminator)')
        print()

        # kludge:
        if op_name in ['ToBoolean', 'ToNumber', 'ToString', 'ToObject', 'RequireObjectCoercible']:
            # not ToBigInt
            assert isinstance(discriminator, NamedType)
            # in_env = init_env.with_expr_type_narrowed('_argument_', discriminator)
            in_env = init_env.copy()
            in_env.vars['_argument_'] = discriminator
        else:
            in_env = init_env

        if body.prod.lhs_s in ['{EMU_ALG_BODY}', '{IND_COMMANDS}', '{EE_RULE}', '{ONE_LINE_ALG}']:
            assert tc_nonvalue(body, in_env) is None
        elif body.prod.lhs_s in ['{EXPR}', '{NAMED_OPERATION_INVOCATION}', '{RHSS}']:
            (out_t, out_env) = tc_expr(body, in_env)
            proc_add_return(out_env, out_t, body)
        else:
            assert 0, body.prod.lhs_s

        # if trace_this_op: pdb.set_trace()

    proc_return_envs = proc_return_envs_stack.pop()

    rr_envs = []
    for return_env in proc_return_envs:
        rr_envs.append(return_env.reduce(header_names))
    final_env = envs_or(rr_envs)

    if op_name == 'Early Errors':
        assert final_env is None
        return None

    assert final_env is not None

    if T_Top_.is_a_subtype_of_or_equal_to(final_env.vars['*return*']):
        print()
        for e in rr_envs:
            print(e.vars['*return*'])
        #? assert 0, final_env.vars['*return*']

    return final_env

def proc_add_return(env_at_return_point, type_of_returned_value, node):
    if trace_this_op:
        print("Type of returned value:", type_of_returned_value)
        input('hit return to continue ')
        if T_Abrupt.is_a_subtype_of_or_equal_to(type_of_returned_value):
            input('hit return to continue ')
        # if T_throw_.is_a_subtype_of_or_equal_to(type_of_returned_value):
        #     input('hit return to continue ')

    # (or intersect Absent with type_of_returned_value)
#    rt_memtypes = type_of_returned_value.set_of_types()
#    for t in [T_not_set, T_not_passed, T_not_there]:
#        # if t.is_a_subtype_of_or_equal_to(type_of_returned_value):
#        if t in rt_memtypes:
#            add_pass_error(
#                ????,
#                "warning: static type of return value includes `%s`" % str(t)
#            )

    # Check that the return value conforms to the proc's declared return
    if not type_of_returned_value.is_a_subtype_of_or_equal_to(proc_expected_return_type):
        add_pass_error(
            node,
            f"static type of return value is {type_of_returned_value}, should be (a subtype of) {proc_expected_return_type}"
        )

    if type_of_returned_value in [T_Top_, T_Normal]: # , T_TBD]:
        #? assert 0, str(type_of_returned_value)
        pass

    aug_env = env_at_return_point.augmented_with_return_type(type_of_returned_value)

    if 1:
        for (pn, ptype) in sorted(aug_env.vars.items()):
            # if isinstance(ptype, UnionType) and len(ptype.member_types) >= 14:
            #     print("`%s` : # member_types = %d" % (pn, len(ptype.member_types)))
            #     if len(ptype.member_types) == 41: assert 0

            if pn == '*return*' and T_not_returned.is_a_subtype_of_or_equal_to(ptype) and ptype != T_Abrupt | ListType(T_code_unit_) | T_Reference_Record | T_Tangible_ | T_empty_ | T_not_returned:
                add_pass_error(
                    node,
                    "At exit, ST of `%s` is `%s`" % (pn, ptype)
                )

    proc_return_envs_stack[-1].add(aug_env)

# ------------------------------------------------------------------------------

def tc_nonvalue(anode, env0):
    # Return the env that this construct delivers to the 'next' thing
    # (i.e. when/if control leaves this construct 'normally')
    # If control never leaves this construct normally
    # (e.g., it's a Return command), return None.

    if trace_this_op:
        trace_line = anode.source_text()
        trace_line = re.sub(r'\n *', r'\\n ', trace_line)
        trace_line = trace_line[0:80]
        print()
        print("Entering nv:", anode.prod.lhs_s, trace_line)
        mytrace(env0)

    assert isinstance(anode, ANode)
    assert env0 is None or isinstance(env0, Env)
    # But if it's None, you're not going to be able to do much!

    # if anode.prod.lhs_s == '{COMMAND}': stderr('>>>', anode.source_text())

    p = str(anode.prod)
    children = anode.children

    if p in [
        r'{IND_COMMANDS} : {_indent_}{COMMANDS}{_outdent_}',
        r'{COMMANDS} : {_NL_N} {COMMAND}',
        r'{COMMAND} : {IF_CLOSED}',
        r'{COMMAND} : {IF_OTHER}',
        r'{ELSE_PART} : Else, {SMALL_COMMAND}.',
        r'{ELSE_PART} : Else,{IND_COMMANDS}',
        r'{ELSE_PART} : Otherwise, {SMALL_COMMAND}.',
        r"{COMMAND} : Perform the following substeps in an implementation-defined order, possibly interleaving parsing and error detection:{IND_COMMANDS}",

        r"{COMMAND} : Optionally, {SMALL_COMMAND}.",
        r"{ONE_LINE_ALG} : {_indent_}{nlai}{COMMAND}{_outdent_}{nlai}",
    ]:
        [child] = children
        result = tc_nonvalue(child, env0)

    elif p == r"{ONE_LINE_ALG} : {_indent_}{nlai}{COMMAND}{nlai}{h_emu_note}{_outdent_}{nlai}":
        [command, note] = children
        tc_nonvalue(command, env0)
        result = None

    elif p == r"{ONE_LINE_ALG} : {_indent_}{nlai}<p>{COMMAND}</p>{nlai}<p>{COMMAND}</p>{_outdent_}{nlai}":
        [com1, com2] = children
        env1 = tc_nonvalue(com1, env0)
        tc_nonvalue(com2, env1)
        result = None

    elif p == r"{ELSE_PART} : Else, {CONDITION_1}. {COMMAND}":
        [cond, comm] = children
        (t_env, f_env) = tc_cond(cond, env0, asserting=True)
        result = tc_nonvalue(comm, t_env)

    elif p == r'{EMU_ALG_BODY} : {IND_COMMANDS}{nlai}':
        [ind_commands] = children
        env1 = tc_nonvalue(ind_commands, env0)
        if env1 is not None:
            # Control falls off the end of the algorithm.
            add_pass_error(
                ind_commands,
                "Control falls off the end of the algorithm (need an explicit Return?)"
            )
            default_return_value = T_not_returned # or T_TildeUnused_, see PR #2397
            proc_add_return(env1, default_return_value, ind_commands)
            result = None
        else:
            # All control paths end with a 'Return'
            result = None

    elif p == r'{COMMANDS} : {COMMANDS}{_NL_N} {COMMAND}':
        [commands, command] = children
        env1 = tc_nonvalue(commands, env0)
        env2 = tc_nonvalue(command, env1)
        result = env2

    # ---------------------------------
    # constructs that create a metavariable

    # Let {var} be ...

    elif p in [
        r"{COMMAND} : Let {var} be {EXPR}. (It may be evaluated repeatedly.)",
        r"{COMMAND} : Let {var} be {EXPR}.",
        r"{COMMAND} : Let {var} be {MULTILINE_EXPR}",
        r"{SMALL_COMMAND} : let {var} be {EXPR}",
        r"{SMALL_COMMAND} : let {var} be {EXPR}, indicating that an ordinary object should be created as the global object",
        r"{SMALL_COMMAND} : let {var} be {EXPR}, indicating that {var}'s global `this` binding should be the global object",
    ]:
        [var, expr] = children[0:2]
        [var_name] = var.children

        (expr_t, env1) = tc_expr(expr, env0)

        if var_name in env0.vars:
            add_pass_error(
                anode,
                "re-Let on existing var `%s`. Use Set?" % var_name
            )
            var_t = env0.vars[var_name]
            if expr_t == var_t:
                # but at least we're not changing the type
                result = env1
            elif expr_t == T_TBD:
                result = env1
                add_pass_error(
                    anode,
                    "... also, ignoring the attempt to change the type of var to %s" % str(expr_t)
                )
            elif var_name in ['_v_', '_value_'] and var_t in [T_Normal, T_Tangible_ | T_not_set] and expr_t == T_Undefined:
                # IteratorBindingInitialization, IteratorDestructuringAssignmentEvaluation, others?:
                # This isn't a re-Let,
                # because it's never the case that _v_ is already defined at this point,
                # but my STA isn't smart enough to know that.
                add_pass_error(
                    anode,
                    "... actually, it isn't, but STA isn't smart enough"
                )
                result = env1
            elif expr_t.is_a_subtype_of_or_equal_to(var_t):
                add_pass_error(
                    anode,
                    "... also, this narrows the type of var from %s to %s" % (var_t, expr_t)
                )
                result = env1.with_expr_type_narrowed(var, expr_t)
            else:
                add_pass_error(
                    anode,
                    "... also, this changes the type of var from %s to %s" % (var_t, expr_t)
                )
                result = env1.with_expr_type_replaced(var, expr_t)
        else:
            # The normal case.
            result = env1.plus_new_entry(var, expr_t)

    elif p == r"{COMMAND} : Let {var} be {EXPR}. (However, if {var} is 10 and {var} contains more than 20 significant digits, every significant digit after the 20th may be replaced by a 0 digit, at the option of the implementation; and if {var} is not 2, 4, 8, 10, 16, or 32, then {var} may be an implementation-approximated integer representing the integer value denoted by {var} in radix-{var} notation.)":
        [let_var, expr, rvar, zvar, rvar2, let_var2, zvar2, rvar3] = children
        assert same_source_text(let_var, let_var2)
        assert same_source_text(rvar, rvar2)
        assert same_source_text(rvar, rvar3)
        assert same_source_text(zvar, zvar2)
        (t, env1) = tc_expr(expr, env0)
        result = env1.plus_new_entry(let_var, t)

    elif p == r"{COMMAND} : Let {var} be an integer for which {NUM_EXPR} is as close to zero as possible. If there are two such {var}, pick the larger {var}.":
        [let_var, num_expr, var2, var3] = children
        assert same_source_text(var2, let_var)
        assert same_source_text(var3, let_var)
        new_env = env0.plus_new_entry(let_var, T_MathInteger_)
        new_env.assert_expr_is_of_type(num_expr, T_MathReal_)
        result = new_env

    # Let {var} and {var} ... be ...

    elif p == r"{COMMAND} : Let {var} and {var} be the indirection values provided when this binding for {var} was created.":
        [m_var, n2_var, n_var] = children
        env0.assert_expr_is_of_type(n_var, T_String)
        result = env0.plus_new_entry(m_var, T_Module_Record).plus_new_entry(n2_var, T_String)

    elif p == r"{COMMAND} : Let {var} and {var} be integers such that {CONDITION} and for which {NUM_EXPR} is as close to zero as possible. If there are two such sets of {var} and {var}, pick the {var} and {var} for which {PRODUCT} is larger.":
        [e_var, n_var, cond, num_expr, e_var2, n_var2, e_var3, n_var3, product] = children
        assert same_source_text(e_var2, e_var)
        assert same_source_text(e_var3, e_var)
        assert same_source_text(n_var2, n_var)
        assert same_source_text(n_var3, n_var)
        new_env = env0.plus_new_entry(e_var, T_MathInteger_).plus_new_entry(n_var, T_MathInteger_)
        (t_env, f_env) = tc_cond(cond, new_env)
        t_env.assert_expr_is_of_type(num_expr, T_MathReal_)
        t_env.assert_expr_is_of_type(product, T_MathReal_)
        result = t_env

    elif p in [
        r"{COMMAND} : Let {var}, {var}, and {var} be integers such that {CONDITION}. If there are multiple possibilities for {var}, choose the value of {var} for which {EX} is closest in value to {EX}. If there are two such possible values of {var}, choose the one that is even. Note that {var} is the number of digits in the representation of {var} using radix {var} and that {var} is not divisible by {var}.",
        r"{COMMAND} : Let {var}, {var}, and {var} be integers such that {CONDITION}. Note that the decimal representation of {var} has {SUM} digits, {var} is not divisible by 10, and the least significant digit of {var} is not necessarily uniquely determined by these criteria.",
        r"{COMMAND} : Let {var}, {var}, and {var} be integers such that {CONDITION}. Note that {var} is the number of digits in the representation of {var} using radix {var}, that {var} is not divisible by {var}, and that the least significant digit of {var} is not necessarily uniquely determined by these criteria.",
    ]:
        [vara, varb, varc, cond] = children[0:4]
        env_for_cond = (
            env0.plus_new_entry(vara, T_MathInteger_)
                .plus_new_entry(varb, T_MathInteger_)
                .plus_new_entry(varc, T_MathInteger_)
        )
        (t_env, f_env) = tc_cond(cond, env_for_cond)
        result = env_for_cond

    # ---

    elif p == r"{COMMAND} : Let {var} be the first element of {var} and remove that element from {var}.":
        [item_var, list_var, list_var2] = children
        assert same_source_text(list_var, list_var2)
        env1 = env0.ensure_expr_is_of_type(list_var, ListType(T_Tangible_)) # XXX over-specific
        result = env1.plus_new_entry(item_var, T_Tangible_)

    elif p == r"{COMMAND} : {h_emu_meta_start}Resume the suspended evaluation of {var}{h_emu_meta_end}. Let {var} be the value returned by the resumed computation.":
        [_, ctx_var, _, b_var] = children
        env0.assert_expr_is_of_type(ctx_var, T_execution_context)
        result = env0.plus_new_entry(b_var, T_Tangible_ | T_return_ | T_throw_)

    elif p in [
        r"{COMMAND} : {h_emu_meta_start}Resume the suspended evaluation of {var}{h_emu_meta_end} using {EX} as the result of the operation that suspended it. Let {var} be the Completion Record returned by the resumed computation.",
        r"{COMMAND} : {h_emu_meta_start}Resume the suspended evaluation of {var}{h_emu_meta_end} using {EX} as the result of the operation that suspended it. Let {var} be the value returned by the resumed computation.",
    ]:
        [_, ctx_var, _, resa_ex, resb_var] = children
        env0.assert_expr_is_of_type(ctx_var, T_execution_context)
        env1 = env0.ensure_expr_is_of_type(resa_ex, T_Tangible_ | T_empty_ | T_return_ | T_throw_)
        result = env1.plus_new_entry(resb_var, T_Tangible_)

    elif p == r"{COMMAND} : Find a finite time value {var} such that {CONDITION}; but if this is not possible (because some argument is out of range), return {LITERAL}.":
        [var, cond, literal] = children
        # once, in MakeDay
        env0.assert_expr_is_of_type(literal, T_Number)
        env1 = env0.plus_new_entry(var, T_FiniteNumber_)
        (t_env, f_env) = tc_cond(cond, env1)
        proc_add_return(env1, T_Number, literal)
        result = env1

    # ---
    # parse

    elif p == r"{COMMAND} : Parse {PP_NAMED_OPERATION_INVOCATION} as a JSON text as specified in ECMA-404. Throw a {ERROR_TYPE} exception if it is not a valid JSON text as defined in that specification.":
        [noi, error_type] = children
        env0.assert_expr_is_of_type(noi, T_Unicode_code_points_)
        result = env0

    # ----------------------------------
    # IF stuff

    elif p in [
        r'{IF_CLOSED} : If {CONDITION}, {SMALL_COMMAND}. Otherwise {SMALL_COMMAND}.',
        r'{IF_CLOSED} : If {CONDITION}, {SMALL_COMMAND}. Otherwise, {SMALL_COMMAND}.',
        r'{IF_CLOSED} : If {CONDITION}, {SMALL_COMMAND}; else {SMALL_COMMAND}.',
        r'{IF_CLOSED} : If {CONDITION}, {SMALL_COMMAND}; otherwise {SMALL_COMMAND}.',
        r'{IF_CLOSED} : If {CONDITION}, {SMALL_COMMAND}; otherwise, {SMALL_COMMAND}.',
    ]:
        [cond, t_command, f_command] = children
        (t_env, f_env) = tc_cond(cond, env0)
        t_benv = tc_nonvalue(t_command, t_env)
        f_benv = tc_nonvalue(f_command, f_env)
        result = env_or(t_benv, f_benv)

    elif p == r"{IF_CLOSED} : If {CONDITION}, {SMALL_COMMAND}. If {CONDITION}, {SMALL_COMMAND}.":
        [cond_a, command_a, cond_b, command_b] = children
        (a_t_env, a_f_env) = tc_cond(cond_a, env0)
        a_benv = tc_nonvalue(command_a, a_t_env)
        (b_t_env, b_f_env) = tc_cond(cond_b, a_f_env)
        b_benv = tc_nonvalue(command_b, b_t_env)
        result = envs_or([a_benv, b_benv])

    elif p == r'{IF_CLOSED} : If {CONDITION}, {SMALL_COMMAND}; else if {CONDITION}, {SMALL_COMMAND}; else {SMALL_COMMAND}.':
        [cond_a, command_a, cond_b, command_b, command_c] = children
        (a_t_env, a_f_env) = tc_cond(cond_a, env0)
        a_benv = tc_nonvalue(command_a, a_t_env)
        (b_t_env, b_f_env) = tc_cond(cond_b, a_f_env)
        b_benv = tc_nonvalue(command_b, b_t_env)
        c_benv = tc_nonvalue(command_c, b_f_env)
        result = envs_or([a_benv, b_benv, c_benv])

    elif p == r'{IF_OTHER} : {IF_OPEN}{IF_TAIL}':
        [if_open, if_tail] = children

        benvs = []

        if if_open.prod.rhs_s in [
            r'If {CONDITION}, {SMALL_COMMAND}.',
            # r'If {CONDITION}, then {SMALL_COMMAND}.', # 2218
            r'If {CONDITION}, then{IND_COMMANDS}',
        ]:
            [condition, then_part] = if_open.children[0:2]
            (t_env, f_env) = tc_cond(condition, env0)
            benvs.append( tc_nonvalue(then_part, t_env) )
        else:
            assert 0, str(if_open.prod)

        while True:
            if if_tail.prod.rhs_s == '{_NL_N} {ELSEIF_PART}{IF_TAIL}':
                [elseif_part, next_if_tail] = if_tail.children
                [condition, then_part] = elseif_part.children
                (t_env, f_env) = tc_cond(condition, f_env)
                benvs.append( tc_nonvalue(then_part, t_env) )
                if_tail = next_if_tail

            elif if_tail.prod.rhs_s == '{_NL_N} {ELSE_PART}':
                [else_part] = if_tail.children
                benvs.append( tc_nonvalue(else_part, f_env) )
                break

            elif if_tail.prod.rhs_s == '{EPSILON}':
                [] = if_tail.children
                # This is like "Else, nothing"
                benvs.append( f_env )
                break

            else:
                assert 0

        result = envs_or(benvs)

        if if_open.source_text() == 'If |BooleanLiteral| is the token `true`, return *true*.':
            # After this step, the possibilities for BooleanLiteral have been exhausted,
            # but that's not obvious from the code.
            # todo: change "If" to "Else"?
            result = None

    # ----------------------------------
    # Returning (normally or abruptly)

    elif p in [
        r"{COMMAND} : Return {EXPR} (no conversion).",
        r"{COMMAND} : Return {EXPR}.",
        r"{COMMAND} : Return {EXPR}. This may be of type Reference.",
        r"{COMMAND} : Return {MULTILINE_EXPR}",
        r"{SMALL_COMMAND} : return {EXPR}",
    ]:
        [expr] = children
        (t1, env1) = tc_expr(expr, env0)
        # assert env1 is env0
        if False and trace_this_op:
            print("Return command's expr has type", t1)
        proc_add_return(env1, t1, anode)
        result = None

    elif p in [
        r"{COMMAND} : Throw a {ERROR_TYPE} exception.",
        r"{SMALL_COMMAND} : throw a {ERROR_TYPE} exception because the structure is cyclical",
        r'{SMALL_COMMAND} : throw a {ERROR_TYPE} exception',
    ]:
        [error_type] = children
        proc_add_return(env0, ThrowType(type_for_ERROR_TYPE(error_type)), anode)
        result = None

    # ----------------------------------
    # Iteration

    elif p in [
        r'{COMMAND} : Repeat,{IND_COMMANDS}',
    ]:
        [commands] = children

        env_at_bottom = tc_nonvalue(commands, env0)

        # The only way to leave a condition-less Repeat
        # is via a Return command,
        # so there can't be anything (except maybe a NOTE) after the loop.
        result = None

        # XXX Should repeat the analysis, feeding the bottom env to the top,
        # XXX until no change.
        # XXX (and likewise with other loops)


    elif p in [
        r'{COMMAND} : Repeat, while {CONDITION},{IND_COMMANDS}',
        r"{COMMAND} : Repeat, until {CONDITION},{IND_COMMANDS}",
    ]:
        [cond, commands] = children
        (t_env, f_env) = tc_cond(cond, env0)

        if 'while' in p:
            (stay_env, exit_env) = (t_env, f_env)
        elif 'until' in p:
            (stay_env, exit_env) = (f_env, t_env)
        else:
            assert 0

        bottom_env = tc_nonvalue(commands, stay_env)
        reduced_bottom_env = bottom_env.reduce(stay_env.vars.keys())
        # assert reduced_bottom_env.equals(stay_env)
        result = exit_env

        # hack!:
        if cond.source_text() == '_matchSucceeded_ is *false*': # in RegExpBuiltinExec
            # This case requires that variable _r_, introduced within the loop,
            # survive the loop.
            # (It doesn't have to survive from one iteration to the next,
            # just from the last iteration to after.)
            result = result.plus_new_entry('_r_', T_State)

    elif p == r"{COMMAND} : While {CONDITION}, an implementation may perform the following steps:{IND_COMMANDS}":
        [cond, commands] = children
        (t_env, f_env) = tc_cond(cond, env0)
        bottom_env = tc_nonvalue(commands, t_env)
        reduced_bottom_env = bottom_env.reduce(t_env.vars.keys())
        result = f_env

    elif p in [
        r'{COMMAND} : For each {EACH_THING}, do{IND_COMMANDS}',
        r'{COMMAND} : For each {EACH_THING}, {SMALL_COMMAND}.',
    ]:
        [each_thing, commands] = children

        # generic list:
        if each_thing.prod.rhs_s in [
            r"element {var} of {EX}",
            r"element {var} of {var}, in reverse List order",
        ]:
            [loop_var, collection_expr] = each_thing.children
            (list_type, env1) = tc_expr(collection_expr, env0); assert env1 is env0
            if list_type == T_List:
                # want to assert that this doesn't happen,
                # but _kept_ in %TypedArray%.prototype.filter
                element_type = T_TBD
            elif list_type == T_TBD:
                element_type = T_TBD
            else:
                assert isinstance(list_type, ListType), list_type
                element_type = list_type.element_type
            env_for_commands = env1.plus_new_entry(loop_var, element_type)

        # ---------------------

        elif each_thing.prod.rhs_s in [
            "{ITEM_NATURE} {var} of {EX}",
            "{ITEM_NATURE} {var} that is an element of {EX}",
        ]:
            [item_nature, loop_var, collection_expr] = each_thing.children

            if item_nature.prod.rhs_s == "code point":
                item_type = T_code_point_
                collection_type = T_Unicode_code_points_

            elif item_nature.prod.rhs_s == r"event":
                item_type = T_event_
                collection_type = T_Set | ListType(T_event_)

            elif item_nature.prod.rhs_s == r"ReadSharedMemory or ReadModifyWriteSharedMemory event":
                item_type = T_ReadSharedMemory_event | T_ReadModifyWriteSharedMemory_event
                collection_type = T_Set

            elif item_nature.prod.rhs_s == "{nonterminal}":
                [nont] = item_nature.children
                item_type = ptn_type_for(nont)
                collection_type = ListType(T_Parse_Node)

            elif item_nature.prod.rhs_s == "Record { {DSBN}, {DSBN} }":
                [dsbn1, dsbn2] = item_nature.children
                dsbns = (dsbn1.source_text(), dsbn2.source_text())
                if dsbns == ('[[Module]]', '[[ExportName]]'):
                    item_type = T_ExportResolveSet_Record_
                elif dsbns == ('[[Key]]', '[[Value]]'):
                    # hack:
                    if collection_expr.source_text() == '_importMetaValues_':
                        item_type = T_ImportMeta_record_ # PR 1892
                    elif collection_expr.source_text() == '_entries_':
                        item_type = T_MapData_record_
                    else:
                        assert 0, collection_expr
                else:
                    assert 0, dsbns
                collection_type = ListType(item_type)

            elif item_nature.prod.rhs_s == r"Record { {DSBN}, {DSBN}, {DSBN} }":
                [dsbn1, dsbn2, dsbn3] = item_nature.children
                assert dsbn1.source_text() == '[[WeakRefTarget]]'
                assert dsbn2.source_text() == '[[HeldValue]]'
                assert dsbn3.source_text() == '[[UnregisterToken]]'
                item_type = T_FinalizationRegistryCellRecord_
                collection_type = ListType(item_type)

            else:
                item_type = {
                    "Agent Events Record" : T_Agent_Events_Record,
                    "Cyclic Module Record": T_Cyclic_Module_Record,
                    "ExportEntry Record"  : T_ExportEntry_Record,
                    "ImportEntry Record"  : T_ImportEntry_Record,
                    "Module Record"       : T_Module_Record,
                    "Parse Node"          : T_Parse_Node,
                    "Private Name"        : T_Private_Name,
                    "PrivateElement"      : T_PrivateElement,
                    "String"              : T_String,
                    "integer"             : T_MathInteger_,
                }[item_nature.prod.rhs_s]
                collection_type = ListType(item_type)

            env1 = env0.ensure_expr_is_of_type(collection_expr, collection_type)
            env_for_commands = env1.plus_new_entry(loop_var, item_type)

        # ------------------------
        # property keys of an object:

        elif each_thing.prod.rhs_s == r"own property key {var} of {var} that is an array index, whose numeric value is greater than or equal to {var}, in descending numeric index order":
            [loop_var, obj_var, lo_var] = each_thing.children
            env0.assert_expr_is_of_type(obj_var, T_Object)
            env0.assert_expr_is_of_type(lo_var, T_Number)
            env_for_commands = env0.plus_new_entry(loop_var, T_String)

        elif each_thing.prod.rhs_s in [
            r"own property key {var} of {var} such that {CONDITION}, in ascending numeric index order",
            r"own property key {var} of {var} such that {CONDITION}, in ascending chronological order of property creation",
        ]:
            [loop_var, obj_var, condition] = each_thing.children
            env0.assert_expr_is_of_type(obj_var, T_Object)
            env1 = env0.plus_new_entry(loop_var, T_String | T_Symbol)
            (tenv, fenv) = tc_cond(condition, env1)
            env_for_commands = tenv

        elif each_thing.prod.rhs_s == r"property of the Global Object specified in clause {h_emu_xref}":
            [emu_xref] = each_thing.children
            # no loop_var!
            env_for_commands = env0

        # -----------------------
        # other collections:

        elif each_thing.prod.rhs_s == r"index {var} of {var}":
            [loop_var, collection_var] = each_thing.children
            env0.assert_expr_is_of_type(collection_var, T_Shared_Data_Block)
            env_for_commands = env0.plus_new_entry(loop_var, T_MathInteger_)

        elif each_thing.prod.rhs_s == r"{nonterminal} {var} that {var} contains":
            [nont, loop_var, root_var] = each_thing.children
            env0.assert_expr_is_of_type(root_var, T_Parse_Node)
            env_for_commands = env0.plus_new_entry(loop_var, ptn_type_for(nont))

        elif each_thing.prod.rhs_s == r"field of {var}":
            [desc_var] = each_thing.children
            loop_var = None # todo: no loop variable!
            env0.assert_expr_is_of_type(desc_var, T_Property_Descriptor)
            env_for_commands = env0

        # --------------------------------------------------
        # things from a large (possibly infinite) set, those that satisfy a condition:

        elif each_thing.prod.rhs_s in [
            r"{ITEM_NATURE} {var} such that {CONDITION}",
            r"{ITEM_NATURE} {var} such that {CONDITION}, in ascending order",
        ]:
            [item_nature, loop_var, condition] = each_thing.children
            item_type = {
                "FinalizationRegistry": T_FinalizationRegistry_object_,
                "WeakMap"             : T_WeakMap_object_,
                "WeakRef"             : T_WeakRef_object_,
                "WeakSet"             : T_WeakSet_object_,
                "event"               : T_Shared_Data_Block_event,
                "integer"             : T_MathInteger_,
            }[item_nature.prod.rhs_s]
            env1 = env0.plus_new_entry(loop_var, item_type)
            (tenv, fenv) = tc_cond(condition, env1)
            env_for_commands = tenv

        elif each_thing.prod.rhs_s == r"integer {var} starting with {EX} such that {CONDITION}, in ascending order":
            [loop_var, start_ex, condition] = each_thing.children
            env0.assert_expr_is_of_type(start_ex, T_MathInteger_)
            env1 = env0.plus_new_entry(loop_var, T_MathInteger_)
            (tenv, fenv) = tc_cond(condition, env1)
            env_for_commands = tenv

        elif each_thing.prod.rhs_s == r"non-negative integer {var} starting with {var} such that {CONDITION}, in descending order":
            [loop_var, start_ex, condition] = each_thing.children
            env0.assert_expr_is_of_type(start_ex, T_MathNonNegativeInteger_)
            env1 = env0.plus_new_entry(loop_var, T_MathNonNegativeInteger_)
            (tenv, fenv) = tc_cond(condition, env1)
            env_for_commands = tenv

        elif each_thing.prod.rhs_s == r"child node {var} of this Parse Node":
            [loop_var] = each_thing.children
            env1 = env0.plus_new_entry(loop_var, T_Parse_Node)
            env_for_commands = env1

        else:
            stderr()
            stderr("each_thing:")
            stderr('        elif each_thing.prod.rhs_s == r"%s":' % each_thing.prod.rhs_s)
            sys.exit(0)

        # --------------------------------------------------

        env_after_commands = tc_nonvalue(commands, env_for_commands)
        # XXX do I need to feed this back somehow?

        # Assume the loop-var doesn't survive the loop
        # if loop_var:
        #     result = env_after_commands.with_var_removed(loop_var)
        # else:
        #     result = env_after_commands

        # The only variables that 'exit' the loop are those that existed beforehand.
        names = env0.vars.keys()
        result = env_after_commands.reduce(names)

    # ----------------------------------
    # Assert

    elif p in [
        r'{COMMAND} : Assert: {CONDITION}.',
    ]:
        [condition] = children
        (t_env, f_env) = tc_cond(condition, env0, asserting=True)
        # throw away f_env
        result = t_env

    elif p in [
        r"{COMMAND} : Assert: If {CONDITION}, then {CONDITION}.",
        r"{COMMAND} : Assert: If {CONDITION}, {CONDITION}.",
    ]:
        [cond1, cond2] = children
        (t1_env, f1_env) = tc_cond(cond1, env0)
        (t2_env, f2_env) = tc_cond(cond2, t1_env, asserting=True)
        result = env_or(f1_env, t2_env)

    elif p == r"{COMMAND} : Assert: {CONDITION_1} if and only if {CONDITION_1}.":
        [cond1, cond2] = children
        (t1_env, f1_env) = tc_cond(cond1, env0)
        (t2_env, f2_env) = tc_cond(cond2, env0)
        result = env_or(
            env_and(t1_env, t2_env),
            env_and(f1_env, f2_env)
        )

    elif p == r"{COMMAND} : Assert: {CONDITION_1} if {CONDITION_1}; otherwise, {CONDITION_1}.":
        [cond_t, cond_x, cond_f] = children
        (xt_env, xf_env) = tc_cond(cond_x, env0)
        (tt_env, tf_env) = tc_cond(cond_t, xt_env, asserting=True)
        (ft_env, ff_env) = tc_cond(cond_f, xf_env, asserting=True)
        result = env_or(tt_env, ft_env)

    # ----------------------------------
    # execution context

    elif p == r'{COMMAND} : Push {var} onto the execution context stack; {var} is now the running execution context.':
        [var1, var2] = children
        assert var1.children == var2.children
        env1 = env0.ensure_expr_is_of_type(var1, T_execution_context)
        result = env1

    elif p == r'{COMMAND} : Remove {var} from the execution context stack and restore the execution context that is at the top of the execution context stack as the running execution context.':
        [var] = children
        env0.assert_expr_is_of_type(var, T_execution_context)
        result = env0

    elif p == r"{COMMAND} : Remove {var} from the execution context stack and restore {var} as the running execution context.":
        [avar, bvar] = children
        env0.assert_expr_is_of_type(avar, T_execution_context)
        env0.assert_expr_is_of_type(bvar, T_execution_context)
        result = env0

    elif p == r"{COMMAND} : Remove {var} from the execution context stack.":
        [avar] = children
        env0.assert_expr_is_of_type(avar, T_execution_context)
        result = env0

    elif p == r"{COMMAND} : Resume the context that is now on the top of the execution context stack as the running execution context.":
        [] = children
        result = env0

    elif p == r"{COMMAND} : Suspend {var} and remove it from the execution context stack.":
        [var] = children
        env0.assert_expr_is_of_type(var, T_execution_context)
        result = env0

    elif p in [
        r"{COMMAND} : Suspend the running execution context.",
    ]:
        [] = children
        result = env0

    elif p == r'{SMALL_COMMAND} : suspend {var}':
        [var] = children
        env0.assert_expr_is_of_type(var, T_execution_context)
        result = env0

    elif p == r'{COMMAND} : Suspend {var}.':
        [var] = children
        result = env0.ensure_expr_is_of_type(var, T_execution_context)

    elif p == r"{COMMAND} : Set {SETTABLE} such that when evaluation is resumed for that execution context the following steps will be performed:{IND_COMMANDS}":
        [settable, commands] = children
        env0.assert_expr_is_of_type(settable, T_host_defined_)
        defns = [(None, commands)]
        env_at_bottom = tc_proc(None, defns, env0)
        result = env0

    elif p == r'{COMMAND} : Set {SETTABLE} such that when evaluation is resumed with a Completion Record {var} the following steps will be performed:{IND_COMMANDS}':
        [settable, comp_var, commands] = children
        env0.assert_expr_is_of_type(settable, T_host_defined_)
        #
        env_for_commands = env0.plus_new_entry(comp_var, T_Tangible_ | T_throw_)
        defns = [(None, commands)]
        env_at_bottom = tc_proc(None, defns, env_for_commands)
        #
        result = env0

    elif p == r"{COMMAND} : Perform any necessary implementation-defined initialization of {var}.":
        [var] = children
        env0.assert_expr_is_of_type(var, T_execution_context)
        result = env0

    elif p == r'{COMMAND} : Once a generator enters the {tilded_word} state it never leaves it and its associated execution context is never resumed. Any execution state associated with {var} can be discarded at this point.':
        [tw, var] = children
        assert tw.source_text() == '~completed~'
        env0.assert_expr_is_of_type(var, T_Object)
        result = env0

    # ----------------------------------

    elif p in [
        r'{COMMAND} : Set {SETTABLE} to {EXPR}.',
        r'{COMMAND} : Set {SETTABLE} to {MULTILINE_EXPR}',
        r'{SMALL_COMMAND} : set {SETTABLE} to {EXPR}',
    ]:
        [settable, expr] = children
        result = env0.set_A_to_B(settable, expr)

    elif p == r'{COMMAND} : Set all of the bytes of {var} to 0.':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_Data_Block)
        result = env1

    elif p == r'{COMMAND} : Wait until no agent is in the critical section for {var}, then enter the critical section for {var} (without allowing any other agent to enter).':
        [var1, var2] = children
        [var_name1] = var1.children
        [var_name2] = var2.children
        assert var_name1 == var_name2
        env1 = env0.ensure_expr_is_of_type(var1, T_WaiterList)
        result = env1

    elif p in [
        r"{COMMAND} : Set {var}'s essential internal methods to the default ordinary object definitions specified in {h_emu_xref}.",
        r"{COMMAND} : Set {var}'s essential internal methods to the definitions specified in {h_emu_xref}.",
    ]:
        [var, emu_xref] = children
        env1 = env0.ensure_expr_is_of_type(var, T_Object)
        result = env1

    elif p in [
        r"{COMMAND} : Append {EX} as an element of {var}.",
        r"{COMMAND} : Append {EX} to the end of {EX}.",
        r"{COMMAND} : Append {EX} to {EX}.",
        r"{COMMAND} : Insert {var} as the first element of {var}.",
        r"{COMMAND} : Prepend {var} to {var}.",
        r"{SMALL_COMMAND} : append {EX} to {var}",
    ]:
        [value_ex, list_ex] = children
        result = env0.ensure_A_can_be_element_of_list_B(value_ex, list_ex)

    elif p == r"{COMMAND} : Append the pair (a two element List) consisting of {var} and {var} to the end of {var}.":
        [avar, bvar, list_var] = children
        env0.assert_expr_is_of_type(avar, T_String | T_Symbol)
        env0.assert_expr_is_of_type(bvar, T_Property_Descriptor)
        (list_type, env1) = tc_expr(list_var, env0); assert env1 is env0
        assert list_type == T_List
        result = env0.with_expr_type_narrowed(list_var, ListType(ListType(T_TBD)))

    elif p == r"{COMMAND} : Append to {var} the elements of {var}.":
        [lista, listb] = children
        env0.assert_expr_is_of_type(lista, ListType(T_SlotName_))
        env0.assert_expr_is_of_type(listb, ListType(T_SlotName_))
        result = env0

    elif p == r'{COMMAND} : Append to {var} each element of {var} that is not already an element of {var}.':
        [vara, varb, varc] = children
        (vara_type, enva) = tc_expr(vara, env0); assert enva is env0
        (varb_type, envb) = tc_expr(varb, env0); assert envb is env0
        (varc_type, envc) = tc_expr(varc, env0); assert envc is env0
        if vara_type == T_TBD and varb_type == T_TBD and varc_type == T_TBD:
            pass
        else:
            assert vara_type.is_a_subtype_of_or_equal_to(T_List)
            assert vara_type == varb_type
            assert varb_type == varc_type
        result = env0

    elif p in [
        r'{COMMAND} : Set {DOTTING} as described in {h_emu_xref}.',
        r'{COMMAND} : Set {DOTTING} as specified in {h_emu_xref}.',
        r'{COMMAND} : Set {DOTTING} to the definition specified in {h_emu_xref}.',
    ]:
        [dotting, emu_xref] = children

        # (t, env1) = tc_expr(settable, env0); assert env1 is env0
        # XXX: could check that emu_xref is sensible for t, but not really worth it?

        mo = re.fullmatch(r'<emu-xref href="#([^"<>]+)"></emu-xref>', emu_xref.source_text())
        sec_id = mo.group(1)
        implied_base_t = {
            # 10.2.*
            'sec-ecmascript-function-objects-call-thisargument-argumentslist'                        : T_function_object_,
            'sec-ecmascript-function-objects-construct-argumentslist-newtarget'                      : T_constructor_object_,

            # 10.3.2
            'sec-built-in-function-objects-construct-argumentslist-newtarget'                        : T_function_object_,

            # 10.4.1.*
            'sec-bound-function-exotic-objects-call-thisargument-argumentslist'                      : T_bound_function_exotic_object_,
            'sec-bound-function-exotic-objects-construct-argumentslist-newtarget'                    : T_bound_function_exotic_object_,

            # 10.4.2.*
            'sec-array-exotic-objects-defineownproperty-p-desc'                                      : T_Array_object_,

            # 10.4.3.*
            'sec-string-exotic-objects-getownproperty-p'                                             : T_String_exotic_object_,
            'sec-string-exotic-objects-defineownproperty-p-desc'                                     : T_String_exotic_object_,
            'sec-string-exotic-objects-ownpropertykeys'                                              : T_String_exotic_object_,

            # 10.4.4.*
            'sec-arguments-exotic-objects-getownproperty-p'                                          : T_Object,
            'sec-arguments-exotic-objects-defineownproperty-p-desc'                                  : T_Object,
            'sec-arguments-exotic-objects-get-p-receiver'                                            : T_Object,
            'sec-arguments-exotic-objects-set-p-v-receiver'                                          : T_Object,
            'sec-arguments-exotic-objects-delete-p'                                                  : T_Object,

            # 10.4.5.*
            'sec-integer-indexed-exotic-objects-getownproperty-p'                                    : T_Integer_Indexed_object_,
            'sec-integer-indexed-exotic-objects-hasproperty-p'                                       : T_Integer_Indexed_object_,
            'sec-integer-indexed-exotic-objects-defineownproperty-p-desc'                            : T_Integer_Indexed_object_,
            'sec-integer-indexed-exotic-objects-get-p-receiver'                                      : T_Integer_Indexed_object_,
            'sec-integer-indexed-exotic-objects-set-p-v-receiver'                                    : T_Integer_Indexed_object_,
            'sec-integer-indexed-exotic-objects-delete-p'                                            : T_Integer_Indexed_object_,
            'sec-integer-indexed-exotic-objects-ownpropertykeys'                                     : T_Integer_Indexed_object_,

            # 10.5.*
            'sec-proxy-object-internal-methods-and-internal-slots-call-thisargument-argumentslist'   : T_Proxy_exotic_object_,
            'sec-proxy-object-internal-methods-and-internal-slots-construct-argumentslist-newtarget' : T_Proxy_exotic_object_,

        }[sec_id]

        assert dotting.prod.rhs_s == '{var}.{DSBN}'
        [base_var, dsbn] = dotting.children

        (curr_base_t, env1) = tc_expr(base_var, env0); assert env1 is env0
        if curr_base_t == T_Object:
            result = env1.with_expr_type_narrowed(base_var, implied_base_t)
        elif curr_base_t == T_bound_function_exotic_object_ | T_Proxy_exotic_object_ | T_other_function_object_ and implied_base_t == T_constructor_object_:
            result = env1.with_expr_type_replaced(base_var, implied_base_t)
        elif curr_base_t == implied_base_t:
            result = env1
        else:
            assert 0

    elif p == r'{COMMAND} : Leave the critical section for {var}.':
        [var] = children
        env0.assert_expr_is_of_type(var, T_WaiterList)
        result = env0

    elif p == r'{COMMAND} : Create own properties of {var} corresponding to the definitions in {h_emu_xref}.':
        [var, emu_xref] = children
        env0.assert_expr_is_of_type(var, T_Object)
        result = env0

    elif p == r'{SMALL_COMMAND} : reverse the order of the elements of {var}':
        [var] = children
        result = env0.ensure_expr_is_of_type(var, T_List)

    elif p in [
        r'{COMMAND} : Add {var} to {var}.',
        r"{SMALL_COMMAND} : add {var} to {var}",
    ]:
        [item_var, collection_var] = children
        (item_type, env1) = tc_expr(item_var, env0); assert env1 is env0
        (collection_type, env2) = tc_expr(collection_var, env0); assert env2 is env0
        if item_type.is_a_subtype_of_or_equal_to(T_event_) and collection_type == T_Set:
            pass
        else:
            assert 0
        result = env0

    elif p == r'{COMMAND} : {note}':
        result = env0

    elif p == r'{COMMAND} : Create an immutable indirect binding in {var} for {var} that references {var} and {var} as its target binding and record that the binding is initialized.':
        [er_var, n_var, m_var, n2_var] = children
        env0.assert_expr_is_of_type(er_var, T_Environment_Record)
        env0.assert_expr_is_of_type(n_var, T_String)
        env0.assert_expr_is_of_type(m_var, T_Module_Record)
        env0.assert_expr_is_of_type(n2_var, T_String)
        result = env0

    elif p in [
        r"{SMALL_COMMAND} : store the individual bytes of {var} into {var}, starting at {var}[{var}]",
        r"{COMMAND} : Store the individual bytes of {var} into {var}, starting at {var}[{var}].",
    ]:
        [var1, var2, var3, var4] = children
        env0.assert_expr_is_of_type(var1, ListType(T_MathInteger_))
        env1 = env0.ensure_expr_is_of_type(var2, T_Data_Block)
        assert var3.children == var2.children
        env0.assert_expr_is_of_type(var4, T_MathInteger_)
        result = env1

    elif p == r"{COMMAND} : Perform {PP_NAMED_OPERATION_INVOCATION} and suspend {var} for up to {var} milliseconds, performing the combined operation in such a way that a notification that arrives after the critical section is exited but before the suspension takes effect is not lost. {var} can notify either because the timeout expired or because it was notified explicitly by another agent calling NotifyWaiter with arguments {var} and {var}, and not for any other reasons at all.":
        [noi, w_var, t_var, *blah] = children
        env0.assert_expr_is_of_type(noi, T_TildeUnused_)
        env0.assert_expr_is_of_type(w_var, T_agent_signifier_)
        env0.assert_expr_is_of_type(t_var, T_MathNonNegativeInteger_)
        result = env0

    elif p in [
        r"{COMMAND} : Perform {PP_NAMED_OPERATION_INVOCATION}.",
        r"{COMMAND} : Perform {PP_NAMED_OPERATION_INVOCATION}. {note}",
        r"{SMALL_COMMAND} : perform {PP_NAMED_OPERATION_INVOCATION}",
    ]:
        noi = children[0]
        (noi_t, env1) = tc_expr(noi, env0, expr_value_will_be_discarded=True)
        if noi_t.is_a_subtype_of_or_equal_to(T_TildeUnused_ | T_Undefined | T_empty_):
            pass
        else:
            if 0:
                # disable because it's noisy for no benefit?
                add_pass_error(
                    anode,
                    "`Perform/Call` discards `%s` value"
                    % str(noi_t)
                )
        result = env1

    elif p == r"{COMMAND} : Create an own {PROPERTY_KIND} property named {var} of object {var} whose {dsb_word}, {dsb_word}, {dsb_word}, and {dsb_word} attributes are set to the value of the corresponding field in {var} if {var} has that field, or to the attribute's {h_emu_xref} otherwise.":
        [kind, name_var, obj_var, *dsbw_, desc_var, desc_var2, emu_xref] = children
        assert desc_var.source_text() == desc_var2.source_text()
        env0.ensure_expr_is_of_type(name_var, T_String | T_Symbol)
        env0.assert_expr_is_of_type(obj_var, T_Object)
        env0.assert_expr_is_of_type(desc_var, T_Property_Descriptor)
        result = env0

    elif p == r"{COMMAND} : Replace the property named {var} of object {var} with an? {PROPERTY_KIND} property whose {dsb_word} and {dsb_word} attributes are set to {var} and {var}, respectively, and whose {dsb_word} and {dsb_word} attributes are set to the value of the corresponding field in {var} if {var} has that field, or to the attribute's {h_emu_xref} otherwise.":
        [name_var, obj_var, kind, dsbw1, dsbw2, field_var1, field_var2, dsbw3, dsbw4, desc_var, desc_var2, emu_xref] = children
        assert desc_var.source_text() == desc_var2.source_text()
        env0.ensure_expr_is_of_type(name_var, T_String | T_Symbol)
        env0.assert_expr_is_of_type(obj_var, T_Object)
        env0.assert_expr_is_of_type(desc_var, T_Property_Descriptor)
        result = env0

    elif p == r"{SMALL_COMMAND} : set the corresponding attribute of the property named {var} of object {var} to the value of the field":
        [name_var, obj_var] = children
        env0.ensure_expr_is_of_type(name_var, T_String | T_Symbol)
        env0.assert_expr_is_of_type(obj_var, T_Object)
        result = env0

    elif p in [
        r"{COMMAND} : ReturnIfAbrupt({EX}).",
        r"{SMALL_COMMAND} : ReturnIfAbrupt({var})",
    ]:
        [ex] = children
        (ex_t, env1) = tc_expr(ex, env0); assert env1 is env0
        if ex_t == T_TBD:
            # Doesn't make sense to compare_types
            # And a proc_add_return(..., T_TBD) wouldn't help
            result = env1
        else:
            (normal_part_of_ex_t, abnormal_part_of_ex_t) = ex_t.split_by(T_Normal)
            if normal_part_of_ex_t == T_0:
                add_pass_error(
                    anode,
                    "ST of `%s` is `%s`, so could just Return, rather than ReturnIfAbrupt"
                    % (ex.source_text(), ex_t)
                )
            if abnormal_part_of_ex_t == T_0:
                add_pass_error(
                    anode,
                    "STA indicates that calling RIA is unnecessary, because `%s` can't be abrupt"
                    % ex.source_text()
                )

            proc_add_return(env1, abnormal_part_of_ex_t, anode)
            result = env1.with_expr_type_narrowed(ex, normal_part_of_ex_t)

    elif p == r"{COMMAND} : IfAbruptRejectPromise({var}, {var}).":
        [vara, varb] = children
        env0.assert_expr_is_of_type(varb, T_PromiseCapability_Record)
        (ta, tenv) = tc_expr(vara, env0); assert tenv is env0

        env0.assert_expr_is_of_type(vara, T_Normal | T_Abrupt)
        (normal_part_of_ta, abnormal_part_of_ta) = ta.split_by(T_Normal)

        proc_add_return(env0, T_Promise_object_, anode)
        result = env0.with_expr_type_narrowed(vara, normal_part_of_ta)

    elif p == r"{COMMAND} : IfAbruptCloseIterator({var}, {var}).":
        [vara, varb] = children
        env0.assert_expr_is_of_type(vara, T_Normal | T_Abrupt)
        env0.assert_expr_is_of_type(varb, T_Iterator_Record)

        proc_add_return(env0, T_Tangible_ | T_empty_ | T_throw_, anode)

        (ta, tenv) = tc_expr(vara, env0); assert tenv is env0
        (normal_part_of_ta, abnormal_part_of_ta) = ta.split_by(T_Normal)
        result = env0.with_expr_type_narrowed(vara, normal_part_of_ta)

    elif p == r"{COMMAND} : {h_emu_not_ref_Record} that the binding for {var} in {var} has been initialized.":
        [_, key_var, oer_var] = children
        env0.assert_expr_is_of_type(key_var, T_String)
        env0.assert_expr_is_of_type(oer_var, T_Environment_Record)
        result = env0

    elif p in [
        r"{COMMAND} : Create an immutable binding in {var} for {var} and record that it is uninitialized. If {var} is *true*, record that the newly created binding is a strict binding.",
        r"{COMMAND} : Create a mutable binding in {var} for {var} and record that it is uninitialized. If {var} is *true*, record that the newly created binding may be deleted by a subsequent DeleteBinding call.",
    ]:
        [er_var, n_var, s_var] = children
        env0.assert_expr_is_of_type(er_var, T_Environment_Record)
        env0.assert_expr_is_of_type(n_var, T_String)
        env0.assert_expr_is_of_type(s_var, T_Boolean)
        result = env0

    elif p == r"{COMMAND} : Remove the binding for {var} from {var}.":
        [n_var, er_var] = children
        env0.assert_expr_is_of_type(n_var, T_String)
        env0.assert_expr_is_of_type(er_var, T_Environment_Record)
        result = env0

    elif p == r"{SMALL_COMMAND} : remove that element from the {var}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_List)
        result = env0

    elif p == r"{COMMAND} : Remove the own property with name {var} from {var}.":
        [name_var, obj_var] = children
        env0.assert_expr_is_of_type(name_var, T_String | T_Symbol)
        env0.assert_expr_is_of_type(obj_var, T_Object)
        result = env0

    elif p == r"{SMALL_COMMAND} : change its bound value to {var}":
        # once, in SetMutableBinding
        # elliptical
        [var] = children
        env0.assert_expr_is_of_type(var, T_Tangible_)
        result = env0

    elif p == r"{COMMAND} : Perform an implementation-defined debugging action.":
        [] = children
        result = env0

    elif p in [
        r"{COMMAND} : Remove {var} from {var}.",
        r"{COMMAND} : Remove {var} from {DOTTING}.",
    ]:
        [item_var, list_ex] = children
        list_type = env0.assert_expr_is_of_type(list_ex, T_List)
        env0.assert_expr_is_of_type(item_var, list_type.element_type)
        result = env0

    elif p == r"{COMMAND} : Set fields of {DOTTING} with the values listed in {h_emu_xref}. {the_field_names_are_the_names_listed_etc}":
        [var, emu_xref, _] = children
        env0.assert_expr_is_of_type(var, T_Intrinsics_Record)
        result = env0

    elif p == r"{COMMAND} : Remove the last element of {SETTABLE}.":
        [settable] = children
        env0.assert_expr_is_of_type(settable, T_List)
        result = env0

    elif p == r"{COMMAND} : Create any host-defined global object properties on {var}.":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Object)
        result = env0

    # -----

    elif p == r"{COMMAND} : Remove {var} from the list of waiters in {var}.":
        [sig, wl] = children
        env0.assert_expr_is_of_type(sig, T_agent_signifier_)
        env0.assert_expr_is_of_type(wl, T_WaiterList)
        result = env0

    elif p == r"{COMMAND} : Notify the agent {var}.":
        [var] = children
        env0.assert_expr_is_of_type(var, T_agent_signifier_)
        result = env0

    elif p == r"{COMMAND} : Replace the element of {SETTABLE} whose value is {var} with an element whose value is {LITERAL}.":
        [list_var, elem_ex, lit] = children
        env1 = env0.ensure_A_can_be_element_of_list_B(elem_ex, list_var)
        env2 = env1.ensure_A_can_be_element_of_list_B(lit, list_var)
        result = env2

    elif p == r"{SMALL_COMMAND} : remove the first code unit from {var}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_String)
        result = env0

    elif p == r"{COMMAND} : Remove the first two code units from {var}.":
        [var] = children
        env0.assert_expr_is_of_type(var, T_String)
        result = env0

    elif p == r"{COMMAND} : Remove the first element from {var}.":
        [var] = children
        env0.assert_expr_is_of_type(var, T_List)
        result = env0

    elif p == r"{COMMAND} : Remove {var} from the front of {var}.":
        [el_var, list_var] = children
        env1 = env0.ensure_A_can_be_element_of_list_B(el_var, list_var)
        result = env1

    elif p == r"{COMMAND} : Append the code unit elements of {var} to the end of {var}.":
        [a, b] = children
        env0.assert_expr_is_of_type(a, T_String)
        env1 = env0.ensure_expr_is_of_type(b, ListType(T_code_unit_))
        result = env1

    elif p == r"{COMMAND} : Append in List order the elements of {var} to the end of the List {var}.":
        [a, b] = children
        env0.assert_expr_is_of_type(a, T_List)
        env0.assert_expr_is_of_type(b, T_List)
        result = env0

    elif p == r"{COMMAND} : Append {EX} and {EX} to {var}.":
        [pvar, svar, list_var] = children

        # only one occurrence, in RegExp.prototype [ @@replace ]
        assert list_var.source_text() == '_replacerArgs_'

        (list_type, list_env) = tc_expr(list_var, env0); assert list_env is env0
        assert list_type == ListType(T_String)
        # because it was created via: Let _replacerArgs_ be &laquo; _matched_ &raquo;.

        # so this is fine:
        env0.assert_expr_is_of_type(svar, T_String)
        env0.assert_expr_is_of_type(pvar, T_IntegralNumber_)

        result = env0.with_expr_type_replaced(list_var, ListType(T_String | T_IntegralNumber_))

    elif p == r"{COMMAND} : The code points `/` or any {nonterminal} occurring in the pattern shall be escaped in {var} as necessary to ensure that the string-concatenation of {EX}, {EX}, {EX}, and {EX} can be parsed (in an appropriate lexical context) as a {nonterminal} that behaves identically to the constructed regular expression. For example, if {var} is {STR_LITERAL}, then {var} could be {STR_LITERAL} or {STR_LITERAL}, among other possibilities, but not {STR_LITERAL}, because `///` followed by {var} would be parsed as a {nonterminal} rather than a {nonterminal}. If {var} is the empty String, this specification can be met by letting {var} be {STR_LITERAL}.":
        # XXX
        result = env0

    elif p == r"{SMALL_COMMAND} : append {code_unit_lit} as the last code unit of {var}":
        [cu_lit, var] = children
        env0.assert_expr_is_of_type(cu_lit, T_code_unit_)
        env0.assert_expr_is_of_type(var, T_String)
        result = env0

    # explicit-exotics:
    elif p == r"{SMALL_COMMAND} : append each of its elements to {var}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_List)
        result = env0

    elif p == r"{COMMAND} : Set {var}'s essential internal methods, except for {DSBN} and {DSBN}, to the definitions specified in {h_emu_xref}.":
        var = children[0]
        env0.assert_expr_is_of_type(var, T_Object)
        result = env0

    elif p == r"{COMMAND} : Choose any such {var}.":
        [var] = children
        result = env0.ensure_expr_is_of_type(var, T_FinalizationRegistryCellRecord_)

    elif p == r"{COMMAND} : Remove from {var} all characters corresponding to a code point on the right-hand side of the {nonterminal} production.":
        [var, nont] = children
        env0.assert_expr_is_of_type(var, T_CharSet)
        result = env0

    elif p == r"{COMMAND} : Attempt to parse {var} using {var} as the goal symbol, and analyse the parse result for any early error conditions. Parsing and early error detection may be interleaved in an implementation-defined manner.":
        [text_var, goal_var] = children
        env0.assert_expr_is_of_type(text_var, T_Unicode_code_points_)
        env0.assert_expr_is_of_type(goal_var, T_grammar_symbol_)
        result = env0

    elif p == r"{COMMAND} : Sort {var} using an implementation-defined sequence of {h_emu_meta_start}calls to {var}{h_emu_meta_end}. If any such call returns an abrupt completion, stop before performing any further calls to {var} and return that Completion Record.":
        [var, _, comparator, _, comparator] = children
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_Tangible_))
        result = env1

    elif p in [
        r"{EE_RULE} : It is a Syntax Error if {CONDITION}.",
        r"{EE_RULE} : It is an early Syntax Error if {CONDITION}.",
    ]:
        [cond] = children
        tc_cond(cond, env0, False)
        result = None

    elif p == r"{EE_RULE} : <p>{_indent_}{nlai}It is a Syntax Error if {LOCAL_REF} is<br>{nlai}{h_emu_grammar}<br>{nlai}and {LOCAL_REF} ultimately derives a phrase that, if used in place of {LOCAL_REF}, would produce a Syntax Error according to these rules. This rule is recursively applied.{_outdent_}{nlai}</p>":
        [local_ref1, h_emu_grammar, local_ref2, local_ref3] = children
        env0.assert_expr_is_of_type(local_ref1, T_Parse_Node)
        env0.assert_expr_is_of_type(local_ref2, T_Parse_Node)
        env0.assert_expr_is_of_type(local_ref3, T_Parse_Node)
        result = None

    elif p == r"{EE_RULE} : If {CONDITION}, the Early Error rules for {h_emu_grammar} are applied.":
        [cond, h_emu_grammar] = children
        tc_cond(cond, env0, False)
        result = None

    elif p == r"{EE_RULE} : If {CONDITION}, it is a Syntax Error if {CONDITION}.":
        [conda, condb] = children
        (tenv, fenv) = tc_cond(conda, env0, False)
        tc_cond(condb, tenv, False)
        result = None

    elif p == r"{EE_RULE} : <p>It is a Syntax Error if {CONDITION_1} and the following algorithm returns {BOOL_LITERAL}:</p>{nlai}{h_emu_alg}":
        [cond, bool_lit, h_emu_alg] = children
        tc_cond(cond, env0)
        # XXX should check h_emu_alg
        result = None

    elif p in [
        r"{EE_RULE} : It is a Syntax Error if {CONDITION}. Additional early error rules for {G_SYM} within direct eval are defined in {h_emu_xref}.",
        r"{EE_RULE} : It is a Syntax Error if {CONDITION}. Additional early error rules for {G_SYM} in direct eval are defined in {h_emu_xref}.",
    ]:
        [cond, g_sym, h_emu_xref] = children
        tc_cond(cond, env0)
        result = None

    elif p == r"{EE_RULE} : It is a Syntax Error if {CONDITION}. This rule is not applied if {CONDITION}.":
        [conda, condb] = children
        (t_env, f_env) = tc_cond(condb, env0)
        tc_cond(conda, f_env)
        result = None

    elif p == r"{EE_RULE} : For each {nonterminal} {var} in {NAMED_OPERATION_INVOCATION}: It is a Syntax Error if {CONDITION}.":
        [nont, var, noi, cond] = children
        t = ptn_type_for(nont)
        env1 = env0.ensure_expr_is_of_type(noi, ListType(t))
        env2 = env1.plus_new_entry(var, t)
        tc_cond(cond, env2)
        result = None

    elif p == r"{EE_RULE} : {LOCAL_REF} must cover an? {nonterminal}.":
        [local_ref, nont] = children
        env0.assert_expr_is_of_type(local_ref, T_Parse_Node)
        result = None

    elif p == r"{COMMAND} : Replace {var} in {var} with {var}.":
        [ex_var, list_var, rep_var] = children
        env0.assert_expr_is_of_type(list_var, ListType(T_PrivateElement))
        env0.assert_expr_is_of_type(ex_var, T_PrivateElement)
        env0.assert_expr_is_of_type(rep_var, T_PrivateElement)
        result = env0

    elif p == r"{SMALL_COMMAND} : perform any host-defined steps for reporting the error":
        [] = children
        result = env0

    elif p == r"{COMMAND} : Discard all resources associated with the current execution context.":
        [] = children
        result = env0

    else:
        stderr()
        stderr("tc_nonvalue:")
        stderr('    elif p == %s:' % escape(p))
        sys.exit(0)

    assert result is None or isinstance(result, Env)

    if trace_this_op:
        print()
        print("Leaving nv:", trace_line)
        mytrace(result)

    return result

# ------------------------------------------------------------------------------

def tc_cond(cond, env0, asserting=False):
    # returns a tuple of two envs, one for true and one for false

    p = str(cond.prod)

    if trace_this_op:
        print()
        print("Entering c:", p)
        print("           ", cond.source_text())
        mytrace(env0)

    result = tc_cond_(cond, env0, asserting)

    if trace_this_op:
        print()
        print("Leaving c:", p)
        print("          ", cond.source_text())
        mytrace(result[0])

    return result

def tc_cond_(cond, env0, asserting):
    p = str(cond.prod)
    children = cond.children

    #----------------
    # simple unit production

    if p in [
        r'{CONDITION} : {CONDITION_1}',
        r'{CONDITION_1} : {TYPE_TEST}',
        r'{CONDITION_1} : {NUM_COMPARISON}',
    ]:
        [child] = children
        return tc_cond(child, env0, asserting)

    # -------------
    # combining conditions

    elif p in [
        r"{CONDITION} : either {CONDITION_1} or {CONDITION_1}",
        r"{CONDITION} : {CONDITION_1} or if {CONDITION_1}",
        r"{CONDITION} : {CONDITION_1} or {CONDITION_1} or {CONDITION_1} or {CONDITION_1}",
        r"{CONDITION} : {CONDITION_1} or {CONDITION_1} or {CONDITION_1}",
        r"{CONDITION} : {CONDITION_1} or {CONDITION_1}",
        r"{CONDITION} : {CONDITION_1}, or if {CONDITION_1}",
        r"{CONDITION} : {CONDITION_1}, or {CONDITION_1}",
        r"{CONDITION} : {CONDITION_1}, {CONDITION_1}, or {CONDITION_1}",
        r"{CONDITION} : {CONDITION_1}, {CONDITION_1}, {CONDITION_1}, or {CONDITION_1}",
    ]:
        logical = ('or', children)
        return tc_logical(logical, env0, asserting)

    elif p in [
        r"{CONDITION} : {CONDITION_1} and if {CONDITION_1}",
        r'{CONDITION} : {CONDITION_1} and {CONDITION_1}',
        r"{CONDITION} : {CONDITION_1} and {CONDITION_1} and {CONDITION_1}",
        r"{CONDITION} : {CONDITION_1}, {CONDITION_1}, and {CONDITION_1}",
        r'{CONDITION} : {CONDITION_1}, {CONDITION_1}, {CONDITION_1}, and {CONDITION_1}',
    ]:
        logical = ('and', children)
        return tc_logical(logical, env0, asserting)

    elif p in [
        r"{CONDITION} : {CONDITION_1}, or if {CONDITION_1} and {CONDITION_1}",
    ]:
        [conda, condb, condc] = children
        logical = (
            'or',
            [
                conda,
                ('and', [condb, condc])
            ]
        )
        return tc_logical(logical, env0, asserting)

    elif p == r"{CONDITION} : {CONDITION_1} or {CONDITION_1} <ins>and {CONDITION_1}</ins>":
        [a, b, c] = children
        logical = (
            'and',
            [
                ('or', [a, b]),
                c
            ]
        )
        return tc_logical(logical, env0, asserting)

    elif p in [
        r"{CONDITION} : {CONDITION_1} and {CONDITION_1} or {CONDITION_1} and {CONDITION_1}",
        r"{CONDITION} : {CONDITION_1} and {CONDITION_1}, or if {CONDITION_1} and {CONDITION_1}",
        r"{CONDITION} : {CONDITION_1} and {CONDITION_1}, or {CONDITION_1} and {CONDITION_1}",
    ]:
        [a, b, c, d] = children
        logical = (
            'or',
            [
                ('and', [a, b]),
                ('and', [c, d]),
            ]
        )
        return tc_logical(logical, env0, asserting)

    elif p == r"{CONDITION} : ({NUM_COMPARISON} or {NUM_COMPARISON}) and ({NUM_COMPARISON} or {NUM_COMPARISON})":
        [a, b, c, d] = children
        logical = (
            'and',
            [
                ('or', [a, b]),
                ('or', [c, d]),
            ]
        )
        return tc_logical(logical, env0, asserting)

    # ---------------
    # Type-conditions

    elif p == r"{CONDITION_1} : {var} has an? {DSBN} or {DSBN} internal slot":
        [var, dsbna, dsbnb] = children
        env0.assert_expr_is_of_type(var, T_Object)
        assert dsbna.source_text() == '[[StringData]]'
        assert dsbnb.source_text() == '[[NumberData]]'
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : {var} has {DSBN} and {DSBN} internal slots",
    ]:
        # XXX could be a type-test
        [var, *dsbn_] = children
        env0.assert_expr_is_of_type(var, T_Object)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} does not have either a {DSBN} or an {DSBN} internal slot":
        [var, dsbna, dsbnb] = children
        env0.assert_expr_is_of_type(var, T_Object)
        return (env0, env0)

    elif p in [
        r'{TYPE_TEST} : Type({TYPE_ARG}) is the same as Type({TYPE_ARG})',
        r'{TYPE_TEST} : Type({TYPE_ARG}) is different from Type({TYPE_ARG})',
    ]:
        # Env can't represent the effect of these.
        # If the incoming static types were different,
        # the 'true' env could at least narrow those to their intersection,
        # but the form only appears twice, and in both cases the static types are the same.
        return (env0, env0)

    # ---

    elif p in [
        r"{CONDITION_1} : {LOCAL_REF} is an? {nonterminal} or an? {nonterminal}",
        r"{CONDITION_1} : {LOCAL_REF} is an? {nonterminal}, an? {nonterminal}, or an? {nonterminal}",
        r"{CONDITION_1} : {LOCAL_REF} is an? {nonterminal}, an? {nonterminal}, an? {nonterminal}, or an? {nonterminal}",
        r"{CONDITION_1} : {LOCAL_REF} is either an? {nonterminal} or an? {nonterminal}",
        r"{CONDITION_1} : {LOCAL_REF} is either an? {nonterminal}, an? {nonterminal}, an? {nonterminal}, or an? {nonterminal}",
        r"{CONDITION_1} : {LOCAL_REF} is neither an? {nonterminal} nor an? {nonterminal}",
        r"{CONDITION_1} : {LOCAL_REF} is neither an? {nonterminal} nor an? {nonterminal} nor an? {nonterminal}",
    ]:
        [local_ref, *nont_] = children
        types = []
        for nonterminal in nont_:
            types.append(ptn_type_for(nonterminal))
        target_t = union_of_types(types)
        copula = 'isnt a' if 'neither' in p else 'is a'
        return env0.with_type_test(local_ref, copula, target_t, asserting)
        # XXX at least some of these are using
        # a more complicated meaning for "is a".

    elif p == r'{CONDITION_1} : {var} is not a {nonterminal}':
        [var, nonterminal] = children
        target_t = ptn_type_for(nonterminal)
        return env0.with_type_test(var, 'isnt a', target_t, asserting)

    # ---

    elif p == r"{CONDITION_1} : {var} is an abrupt completion":
        [var] = children
        return env0.with_type_test(var, 'is a', T_Abrupt, asserting)

    elif p in [
        r"{CONDITION_1} : {var} is never an abrupt completion",
        r"{CONDITION_1} : {var} is not an abrupt completion",
    ]:
        [var] = children
        return env0.with_type_test(var, 'isnt a', T_Abrupt, asserting)

    elif p == r"{CONDITION_1} : {var} is an Abstract Closure with no parameters":
        [var] = children
        return env0.with_type_test(var, 'is a', T_proc_, asserting)

    elif p == r'{CONDITION_1} : {var} is an Array exotic object':
        [var] = children
        return env0.with_type_test(var, 'is a', T_Array_object_, asserting)

    elif p == r'{CONDITION_1} : {var} is a UTF-16 code unit':
        [var] = children
        return env0.with_type_test(var, 'is a', T_code_unit_, asserting)

    elif p == r'{CONDITION_1} : {EX} is a BigInt':
        [ex] = children
        return env0.with_type_test(ex, 'is a', T_BigInt, asserting)

    elif p == r'{CONDITION_1} : {var} is a Boolean':
        [var] = children
        return env0.with_type_test(var, 'is a', T_Boolean, asserting)

    elif p == r"{CONDITION_1} : {var} is a ClassFieldDefinition Record":
        [var] = children
        return env0.with_type_test(var, 'is a', T_ClassFieldDefinition_Record, asserting)

    elif p == r"{CONDITION_1} : {var} is a ClassStaticBlockDefinition Record":
        [var] = children
        return env0.with_type_test(var, 'is a', T_ClassStaticBlockDefinition_Record, asserting)

    elif p == r"{CONDITION_1} : {var} is a Continuation":
        [var] = children
        return env0.with_type_test(var, 'is a', T_Continuation, asserting)

    elif p == r"{CONDITION_1} : {var} is a Cyclic Module Record":
        [var] = children
        return env0.with_type_test(var, 'is a', T_Cyclic_Module_Record, asserting)

    elif p == r"{CONDITION_1} : {var} is not a Cyclic Module Record":
        [var] = children
        return env0.with_type_test(var, 'isnt a', T_Cyclic_Module_Record, asserting)

    elif p == r'{CONDITION_1} : {var} is a Data Block':
        [var] = children
        return env0.with_type_test(var, 'is a', T_Data_Block, asserting)

    elif p == r'{CONDITION_1} : {var} is the execution context of a generator':
        [var] = children
        return env0.with_type_test(var, 'is a', T_execution_context, asserting)

    elif p in [
        r"{CONDITION_1} : {EX} is an Environment Record",
    ]:
        [var] = children
        return env0.with_type_test(var, 'is a', T_Environment_Record, asserting)

    elif p in [
        r"{CONDITION_1} : {var} is an? {ENVIRONMENT_RECORD_KIND} Environment Record",
        r"{CONDITION_1} : {var} is not an? {ENVIRONMENT_RECORD_KIND} Environment Record",
    ]:
        [var, kind] = children
        copula = 'isnt a' if 'not' in p else 'is a'
        return env0.with_type_test(var, copula, type_for_environment_record_kind(kind), asserting)

    elif p == r"{CONDITION_1} : {var} is a possibly empty List":
        [list_var] = children
        return env0.with_type_test(list_var, 'is a', T_List, asserting)

    elif p == r"{CONDITION_1} : {var} is a List of characters":
        [list_var] = children
        return env0.with_type_test(list_var, 'is a', ListType(T_character_), asserting)

    elif p == r"{CONDITION_1} : {var} is a List of property keys":
        [var] = children
        return env0.with_type_test(var, 'is a', ListType(T_String | T_Symbol), asserting)

    elif p == r'{CONDITION_1} : {var} is a List of errors':
        [var] = children
        return env0.with_type_test(var, 'is a', ListType(T_SyntaxError | T_ReferenceError), asserting)

    elif p == r'{CONDITION_1} : {var} is a List of WriteSharedMemory or ReadModifyWriteSharedMemory events with length equal to {EX}':
        [var, ex] = children
        env0.assert_expr_is_of_type(ex, T_MathInteger_)
        return env0.with_type_test(var, 'is a', ListType(T_WriteSharedMemory_event | T_ReadModifyWriteSharedMemory_event), asserting)

    elif p == r"{CONDITION_1} : {var} is a non-empty List of {ERROR_TYPE} objects":
        [var, error_type] = children
        return env0.with_type_test(var, 'is a', ListType(type_for_ERROR_TYPE(error_type)), asserting)

    elif p in [
        r"{CONDITION_1} : {var} is now an empty List",
    ]:
        [var] = children
        env0.assert_expr_is_of_type(var, T_List)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {EX} is a String":
        [ex] = children
        return env0.with_type_test(ex, 'is a', T_String, asserting)

    elif p == r"{CONDITION_1} : {var} is not a String":
        [var] = children
        return env0.with_type_test(var, 'isnt a', T_String, asserting)

    elif p == r"{CONDITION_1} : {var} is a Unicode {h_emu_not_ref_property_name} or property alias listed in the &ldquo;{h_emu_not_ref_Property_name} and aliases&rdquo; column of {h_emu_xref} or {h_emu_xref}":
        [v, _, _, emu_xref1, emu_xref2] = children
        env0.assert_expr_is_of_type(v, ListType(T_code_point_))
        return (env0, env0)

    elif p == r"{CONDITION_1} : {EX} is a sequence of Unicode code points":
        [ex] = children
        env0.assert_expr_is_of_type(ex, T_Unicode_code_points_)
        return (env0, env0)

    elif p in [
        r'{CONDITION_1} : {EX} is present',
        r'{CONDITION_1} : {EX} is not present',
    ]:
        [ex] = children
        if ex.is_a('{PROD_REF}'):
            t = T_not_in_node
        elif ex.is_a('{var}'):
            # todo: get rid of this usage. (roll eyes at PR #953)
            t = T_not_passed # assuming it's a parameter
        else:
            assert 0, ex.source_text()
        copula = 'is a' if 'not present' in p else 'isnt a'
        return env0.with_type_test(ex, copula, t, asserting)

    elif p == r'{CONDITION_1} : {var} is a Number':
        [var] = children
        return env0.with_type_test(var, 'is a', T_Number, asserting)

    elif p == r'{CONDITION_1} : {var} is not a Number':
        [var] = children
        return env0.with_type_test(var, 'isnt a', T_Number, asserting)

    elif p == r'{CONDITION_1} : {EX} is an Object':
        [ex] = children
        return env0.with_type_test(ex, 'is a', T_Object, asserting)

    elif p == r"{CONDITION_1} : {EX} is not an Object":
        [ex] = children
        return env0.with_type_test(ex, 'isnt a', T_Object, asserting)

    elif p == r"{CONDITION_1} : {var} is a Parse Node":
        [var] = children
        return env0.with_type_test(var, 'is a', T_Parse_Node, asserting)

    elif p == r"{CONDITION_1} : {EX} is a Private Name":
        [ex] = children
        return env0.with_type_test(ex, 'is a', T_Private_Name, asserting)

    elif p == r"{CONDITION_1} : {var} is a PrivateElement":
        [var] = children
        return env0.with_type_test(var, 'is a', T_PrivateElement, asserting)

    elif p == r"{CONDITION_1} : {var} is a PromiseCapability Record":
        [var] = children
        return env0.with_type_test(var, 'is a', T_PromiseCapability_Record, asserting)

    elif p == r'{CONDITION_1} : {var} is an? {PROPERTY_KIND} property':
        [var, kind] = children
        t = {
            'accessor': T_accessor_property_,
            'data'    : T_data_property_,
        }[kind.source_text()]
        return env0.with_type_test(var, 'is a', t, asserting)

    elif p in [
        r'{CONDITION_1} : {var} is a Proxy exotic object',
        r"{CONDITION_1} : {var} is a Proxy object",
    ]:
        [var] = children
        return env0.with_type_test(var, 'is a', T_Proxy_exotic_object_, asserting)

    elif p == r'{CONDITION_1} : {var} is a ReadModifyWriteSharedMemory event':
        [var] = children
        return env0.with_type_test(var, 'is a', T_ReadModifyWriteSharedMemory_event, asserting)

    elif p == r'{CONDITION_1} : {var} is a Reference Record':
        [var] = children
        return env0.with_type_test(var, 'is a', T_Reference_Record, asserting)

    elif p == r'{CONDITION_1} : {var} is not a Reference Record':
        [var] = children
        return env0.with_type_test(var, 'isnt a', T_Reference_Record, asserting)

    elif p == r"{CONDITION_1} : {var} is a ResolvedBinding Record":
        [var] = children
        return env0.with_type_test(var, 'is a', T_ResolvedBinding_Record, asserting)

    elif p == r'{CONDITION_1} : {var} is a Shared Data Block':
        [var] = children
        return env0.with_type_test(var, 'is a', T_Shared_Data_Block, asserting)

    elif p == r'{CONDITION_1} : {var} is not a Shared Data Block':
        [var] = children
        return env0.with_type_test(var, 'isnt a', T_Shared_Data_Block, asserting)

    elif p == r'{CONDITION_1} : {var} is a ReadSharedMemory, WriteSharedMemory, or ReadModifyWriteSharedMemory event':
        [var] = children
        return env0.with_type_test(var, 'is a', T_Shared_Data_Block_event, asserting)

    elif p == r"{CONDITION_1} : {var} is a Source Text Module Record":
        [var] = children
        return env0.with_type_test(var, 'is a', T_Source_Text_Module_Record, asserting)

    elif p == r"{CONDITION_1} : {var} is a State":
        [var] = children
        return env0.with_type_test(var, 'is a', T_State, asserting)

    elif p == r'{CONDITION_1} : {var} is a Symbol':
        [var] = children
        return env0.with_type_test(var, 'is a', T_Symbol, asserting)

    elif p == r"{CONDITION_1} : {var} is not a Symbol":
        [var] = children
        return env0.with_type_test(var, 'isnt a', T_Symbol, asserting)

    elif p in [
        r"{CONDITION_1} : {var} is a normal completion with a value of {LITERAL}. The possible sources of this value are Await or, if the async function doesn't await anything, step {h_emu_xref} above",
    ]:
        [var, literal, _] = children
        env0.assert_expr_is_of_type(literal, T_TildeUnused_)
        return env0.with_type_test(var, 'is a', T_TildeUnused_, asserting)

    elif p == r'{CONDITION_1} : {var} is a WriteSharedMemory event':
        [var] = children
        return env0.with_type_test(var, 'is a', T_WriteSharedMemory_event, asserting)

    elif p ==  r"{CONDITION_1} : {var} is a normal completion":
        [var] = children
        return env0.with_type_test(var, 'is a', T_Normal, asserting)

    elif p == r"{CONDITION_1} : {var} is either a String, Number, Boolean, Null, or an Object that is defined by either an {nonterminal} or an {nonterminal}":
        [var, nonta, nontb] = children
        return env0.with_type_test(var, 'is a', T_String | T_Number | T_Boolean | T_Null | T_Object, asserting)

    elif p == r"{CONDITION_1} : {var} is either a String, a Number, a BigInt, or a Symbol":
        [var] = children
        return env0.with_type_test(var, 'is a', T_String | T_Number | T_BigInt | T_Symbol, asserting)

    elif p == r"{CONDITION_1} : {var} is a bound function exotic object":
        [var] = children
        return env0.with_type_test(var, 'is a', T_bound_function_exotic_object_, asserting)

    # ----------------------
    # quasi-type-conditions

    elif p in [
        r'{CONDITION_1} : {var} is an ECMAScript function object',
    ]:
        [var] = children
        return (
            env0.with_expr_type_narrowed(var, T_function_object_),
            env0
        )

    elif p == r"{CONDITION_1} : {var} is a List of a single Number":
        [var] = children
        return (
            env0.with_expr_type_narrowed(var, ListType(T_Number)),
            env0
        )

    elif p in [
        r"{CONDITION_1} : {var} is an instance of the production {h_emu_grammar}",
    ]:
        [local_ref, emu_grammar] = children
        emu_grammar_text = emu_grammar.source_text()
        lhs = re.sub(r'<emu-grammar>(\w+) :.*', r'\1', emu_grammar_text)
        prodn_type = ptn_type_for(lhs)
        #
        (ref_type, env1) = tc_expr(local_ref, env0); assert env1 is env0
        assert prodn_type.is_a_subtype_of_or_equal_to(ref_type)
        # but whether or not it's an instance of that particular production
        # doesn't narrow its type.
        return (env1.with_expr_type_narrowed(local_ref, prodn_type), env1)

    elif p in [
        r"{CONDITION_1} : {var} is an Object that has an? {DSBN} internal slot",
        r'{CONDITION_1} : {var} is an extensible object that does not have a {starred_str} own property',
    ]:
        [var, _] = children
        return (
            env0.with_expr_type_narrowed(var, T_Object),
            env0
        )

    elif p in [
        r"{CONDITION_1} : {var} is an ordinary, extensible object with no non-configurable properties",
        r"{CONDITION_1} : {var} is an extensible ordinary object with no own properties",
    ]:
        [var] = children
        return (
            env0.with_expr_type_narrowed(var, T_Object),
            env0
        )

    elif p == r"{CONDITION_1} : {var} is a non-negative integral Number":
        [var] = children
        return (
            env0.with_expr_type_narrowed(var, T_IntegralNumber_),
            env0
        )

    elif p == "{CONDITION_1} : {var} is a fully populated Property Descriptor":
        [var] = children
        return (
            env0.with_expr_type_narrowed(var, T_Property_Descriptor),
            env0
        )

    elif p in [
        r"{CONDITION_1} : {var} is an integer index",
        r"{CONDITION_1} : {var} is an array index",
    ]:
        [var] = children
        return (
            env0.with_expr_type_narrowed(var, T_String),
            env0
        )

    elif p in [
        r"{CONDITION_1} : {var} is not an array index",
        r"{CONDITION_1} : {var} is not an integer index",
    ]:
        [var] = children
        return (
            env0,
            env0.with_expr_type_narrowed(var, T_String)
        )

    elif p in [
        r"{CONDITION_1} : {var} is a {h_emu_xref}",
        r"{CONDITION_1} : {var} is not a {h_emu_xref}",
    ]:
        [var, emu_xref] = children

        # copula = 'isnt a' if 'not' in p else 'is a'

        if emu_xref.source_text() in [
            '<emu-xref href="#leading-surrogate"></emu-xref>',
            '<emu-xref href="#trailing-surrogate"></emu-xref>',
        ]:
            t = T_code_unit_
        elif emu_xref.source_text() == '<emu-xref href="#sec-built-in-function-objects">built-in function object</emu-xref>':
            t = T_function_object_
        else:
            assert 0

        if 'is a' in p:
            return (
                env0.with_expr_type_narrowed(var, t),
                env0
            )
        else:
            return (
                env0,
                env0.with_expr_type_narrowed(var, t)
            )

    elif p in [
        r"{CONDITION_1} : The value of {SETTABLE} is {LITERAL}",
        r"{CONDITION_1} : {EX} is not {LITERAL}",
        r"{CONDITION_1} : {EX} is {LITERAL}",
        r"{CONDITION_1} : {var} is also {LITERAL}",
        r"{CONDITION_1} : {var} is the value {LITERAL}",
    ]:
        [ex, literal] = children

        # kludgey?
        r = is_simple_call(ex)
        if r:
            (callee_op_name, var) = r
            #
            if callee_op_name == 'IsSharedArrayBuffer':
                t = T_SharedArrayBuffer_object_
            elif callee_op_name == 'IsPromise':
                t = T_Promise_object_
            elif callee_op_name == 'IsCallable':
                t = T_function_object_
            elif callee_op_name == 'IsConstructor':
                t = T_constructor_object_
            elif callee_op_name == 'IsPropertyKey':
                t = T_String | T_Symbol
            elif callee_op_name == 'IsIntegralNumber':
                t = T_IntegralNumber_
            else:
                t = None
            #
            if t:
                assert 'not' not in p
                if literal.source_text() == '*true*':
                    copula = 'is a'
                elif literal.source_text() == '*false*':
                    copula = 'isnt a'
                else:
                    assert 0
                #
                return env0.with_type_test(var, copula, t, asserting)

        copula = 'isnt a' if 'is not' in p else 'is a'

        # special handling for Completion Records:
        while True: # ONCE
            dotting = ex.is_a('{DOTTING}')
            if dotting is None: break
            (lhs, dsbn) = dotting.children
            dsbn_name = dsbn.source_text()[2:-2]
            if dsbn_name != 'Type': break
            t = type_corresponding_to_comptype_literal(literal)
            return env0.with_type_test(lhs, copula, t, asserting)

        # ------------

        (lit_type, lit_env) = tc_expr(literal, env0)
        assert lit_env is env0

        if lit_type in [T_Undefined, T_Null, T_empty_, T_not_in_node, T_match_failure_, T_NaN_Number_, T_MathPosInfinity_, T_MathNegInfinity_, T_TildeAmbiguous_, T_TildeNamespace_, T_TildeAllButDefault_, T_TildeAll_, T_TildeNamespaceObject_]:
            # i.e., the literal is *undefined* or *null* or ~empty~ or ~failure~ or *NaN* or +&infin; or -&infin;
            # Because the type has only one value,
            # a value-comparison is equivalent to a type-comparison.
            return env0.with_type_test(ex, copula, lit_type, asserting)
        else:
            # The type has more than one value.
            # So, while the is-case is type-constraining,
            # the isn't-case isn't.
            is_env = env0.with_expr_type_narrowed(ex, lit_type)
            isnt_env = env0

            if copula == 'is a':
                return (is_env, isnt_env)
            else:
                return (isnt_env, is_env)

    elif p in [
        r'{CONDITION_1} : {EX} is {LITERAL} or {LITERAL}',
        r'{CONDITION_1} : {EX} is either {LITERAL} or {LITERAL}',
        # ---
        r"{CONDITION_1} : {EX} is not {LITERAL} or {LITERAL}",
        r"{CONDITION_1} : {EX} is neither {LITERAL} nor {LITERAL}",
    ]:
        [ex, lita, litb] = children

        # special handling for Completion Records' [[Type]] field
        while True: # ONCE
            dotting = ex.is_a('{DOTTING}')
            if dotting is None: break
            (lhs, dsbn) = dotting.children
            dsbn_name = dsbn.source_text()[2:-2]
            if dsbn_name != 'Type': break
            ta = type_corresponding_to_comptype_literal(lita)
            tb = type_corresponding_to_comptype_literal(litb)
            assert 'never' not in p
            assert 'neither' not in p
            return env0.with_type_test(lhs, 'is a', ta | tb, asserting)

        (lita_type, lita_env) = tc_expr(lita, env0); assert lita_env is env0
        (litb_type, litb_env) = tc_expr(litb, env0); assert litb_env is env0

        copula = 'isnt a' if ('never' in p or 'neither' in p or 'not' in p) else 'is a'

        # It's only a type-test if the literals are from very small types.
        if (
            lita_type == T_Null and litb_type == T_Undefined
            or
            lita_type == T_Undefined and litb_type == T_Null
        ):
            return env0.with_type_test(ex, copula, T_Null | T_Undefined, asserting)

        elif lita_type == T_Null and litb_type == T_TildeAmbiguous_:
            return env0.with_type_test(ex, copula, T_Null | T_TildeAmbiguous_, asserting)

        elif lita_type == litb_type:
            (t, env1) = tc_expr(ex, env0)
            if t == lita_type:
                pass
            else:
                env1 = env1.with_expr_type_replaced(ex, lita_type)
            return (env1, env0)

        elif lita_type == T_Boolean and litb_type == T_Undefined:
            # Evaluation of RelationalExpression: If _r_ is *true* or *undefined*, ...
            env0.assert_expr_is_of_type(ex, T_Boolean | T_Undefined)
            return (env0, env0)

        elif lita_type == T_NaN_Number_ and litb_type == T_InfiniteNumber_:
            return (env0, env0) #XXX

        else:
            assert 0, (lita_type, litb_type)

    elif p == r'{CONDITION_1} : {EX} and {EX} are both {LITERAL}':
        [exa, exb, lit] = children
        (lit_type, lit_env) = tc_expr(lit, env0); assert lit_env is env0
        if lit_type in [T_Undefined, T_NaN_Number_]:
            (a_t_env, a_f_env) = env0.with_type_test(exa, 'is a', lit_type, asserting)
            (b_t_env, b_f_env) = env0.with_type_test(exb, 'is a', lit_type, asserting)
            return (
                env_and(a_t_env, b_t_env),
                env_or(a_f_env, b_f_env)
            )
        else:
            env0.assert_expr_is_of_type(exa, lit_type)
            env0.assert_expr_is_of_type(exb, lit_type)
            return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is an integer":
        [var] = children
        return env0.with_type_test(var, 'is a', T_MathInteger_, asserting)

    elif p == r"{CONDITION_1} : {var} is finite":
        [var] = children
        (t, env1) = tc_expr(var, env0); assert env1 is env0
        if t.is_a_subtype_of_or_equal_to(T_Number):
            return env1.with_type_test(var, 'is a', T_FiniteNumber_, asserting)
        elif t.is_a_subtype_of_or_equal_to(T_ExtendedMathReal_):
            return env1.with_type_test(var, 'is a', T_MathReal_, asserting)
        else:
            assert 0

    elif p == r"{CONDITION_1} : {var} and {var} are both finite":
        [a, b] = children
        (a_t_env, a_f_env) = env0.with_type_test(a, 'is a', T_FiniteNumber_, asserting)
        (b_t_env, b_f_env) = env0.with_type_test(b, 'is a', T_FiniteNumber_, asserting)
        return (
            env_and(a_t_env, b_t_env),
            env_or(a_f_env, b_f_env)
        )

    elif p == r"{CONDITION_1} : {var} is not finite":
        [var] = children
        (t, env1) = tc_expr(var, env0); assert env1 is env0
        if t.is_a_subtype_of_or_equal_to(T_Number | T_BigInt):
            return env1.with_type_test(var, 'isnt a', T_FiniteNumber_, asserting)
        elif t.is_a_subtype_of_or_equal_to(T_ExtendedMathReal_):
            return env1.with_type_test(var, 'isnt a', T_MathReal_, asserting)
        else:
            assert 0

    elif p == r"{CONDITION_1} : {var} and {var} are both WriteSharedMemory or ReadModifyWriteSharedMemory events":
        # XXX spec is ambiguous: "each is A or B" vs "either both A or both B"
        [ea, eb] = children
        (a_t_env, a_f_env) = env0.with_type_test(ea, 'is a', T_WriteSharedMemory_event | T_ReadModifyWriteSharedMemory_event, asserting)
        (b_t_env, b_f_env) = env0.with_type_test(eb, 'is a', T_WriteSharedMemory_event | T_ReadModifyWriteSharedMemory_event, asserting)
        return (
            env_and(a_t_env, b_t_env),
            env_or(a_f_env, b_f_env)
        )

    elif p in [
        r"{CONDITION_1} : {EX} is {LITERAL}, {LITERAL}, or {LITERAL}",
        r"{CONDITION_1} : {EX} is {LITERAL}, {LITERAL}, {LITERAL}, or {LITERAL}",
        r"{CONDITION_1} : {EX} is either {LITERAL}, {LITERAL}, or {LITERAL}",
        r"{CONDITION_1} : {EX} is either {LITERAL}, {LITERAL}, {LITERAL}, or {LITERAL}",
        r"{CONDITION_1} : {var} is one of {LITERAL}, {LITERAL}, {LITERAL}, or {LITERAL}",
        r"{CONDITION_1} : {EX} is {LITERAL}, {LITERAL}, {LITERAL}, {LITERAL}, or {LITERAL}",
        r"{CONDITION_1} : {EX} is {LITERAL}, {LITERAL}, {LITERAL}, {LITERAL}, {LITERAL}, or {LITERAL}",
    ]:
        [var, *lit_] = children
        assert len(lit_) in [3,4,5,6]
        lit_types = []
        for lit in lit_:
            (ti, envi) = tc_expr(lit, env0)
            # assert envi is env0
            lit_types.append(ti)
        lt = union_of_types(lit_types)
        return env0.with_type_test(var, 'is a', lt, asserting)

    elif p == r'{CONDITION_1} : {var} has an? {DSBN} internal method':
        [var, dsbn] = children
        env1 = env0.ensure_expr_is_of_type(var, T_Object)
        dsbn_name = dsbn.source_text()[2:-2]
        if dsbn_name == 'Call':
            # one of the few where the presence/absence of an internal method is a type-test?
            return env1.with_type_test(var, 'is a', T_function_object_, asserting)
        elif dsbn_name == 'Construct':
            return env1.with_type_test(var, 'is a', T_constructor_object_, asserting)
        else:
            assert 0, dsbn_name

    elif p == r"{CONDITION_1} : {SETTABLE} has an? {DSBN} field":
        [settable, dsbn] = children
        dsbn_name = dsbn.source_text()[2:-2]
        t = env0.assert_expr_is_of_type(settable, T_Record)
        if t.name == 'Environment Record' and dsbn_name == 'NewTarget':
            add_pass_error(
                cond,
                "STA can't confirm that `%s` could have a `%s` field"
                % ( settable.source_text(), dsbn_name )
            )
            # We could confirm if we looked at the subtypes and what fields they have.
            return (
                env0.with_expr_type_narrowed(settable, T_Function_Environment_Record),
                env0
            )
        else:
            assert dsbn_name in fields_for_record_type_named_[t.name], (t.name, dsbn_name)
            return (env0, env0)

    elif p == r'{CONDITION_1} : {var} does not have an? {DSBN} field':
        [var, dsbn] = children
        env1 = env0.ensure_expr_is_of_type(var, T_Record)
        # XXX We should check whether its type says it *could* have such a field.
        # XXX The particular DSBN could have a (sub-)type-constraining effect
        return (env1, env1)

    elif p == r'{CONDITION_1} : {var} does not have an? {DSBN} internal slot':
        [var, dsbn] = children
        env1 = env0.ensure_expr_is_of_type(var, T_Object)
        # Whether or not it has that particular slot, it's still an Object.
        # XXX The particular DSBN could have a (sub-)type-constraining effect
        return (env1, env1)

    elif p == r"{CONDITION_1} : {var} does not have an? {var} internal slot":
        [obj_var, slotname_var] = children
        env0.assert_expr_is_of_type(obj_var, T_Object)
        env0.assert_expr_is_of_type(slotname_var, T_SlotName_)
        return (env0, env0)

    elif p in [
        r'{CONDITION_1} : {var} also has a {DSBN} internal slot',
        r'{CONDITION_1} : {var} has an? {DSBN} internal slot',
    ]:
        [var, dsbn] = children
        env1 = env0.ensure_expr_is_of_type(var, T_Object)
        # Whether or not it has that particular slot, it's still an Object.
        # XXX we could be more specific about the sub-kind of Object
        return (env1, env1)

    elif p == r'{CONDITION_1} : {var} is an IEEE 754-2019 binary32 NaN value':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_IEEE_binary32_)
        return (env1, env1)

    elif p == r'{CONDITION_1} : {var} is an IEEE 754-2019 binary64 NaN value':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_IEEE_binary64_)
        return (env1, env1)

    # --------
    # These 4 are affected by the strangeness described in Issue #831

    elif p == r"{CONDITION_1} : {var} is the {nonterminal} {TERMINAL}":
        [var, nont, term] = children
        assert nont.source_text() == '|ReservedWord|'
        assert term.source_text() == "`super`"
        env0.ensure_expr_is_of_type(var, T_grammar_symbol_)
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : {var} is an? {nonterminal}",
        r"{CONDITION_1} : {var} is an? {nonterminal} Parse Node",
    ]:
        [var, nont] = children
        env1 = env0.ensure_expr_is_of_type(var, T_Parse_Node)
        return (env1, env1)
        #return env0.with_type_test(var, 'is a', ptn_type_for(nont), asserting)

    elif p == r"{CONDITION_1} : {var} is {nonterminal}":
        [var, nont] = children
        env1 = env0.ensure_expr_is_of_type(var, T_grammar_symbol_)
        return (env1, env1)

    elif p in [
        r"{CONDITION_1} : {var} is not one of {nonterminal}, {nonterminal}, {nonterminal}, `super` or `this`",
        r"{CONDITION_1} : {var} is not one of {nonterminal}, {nonterminal}, {nonterminal}, `super`, or `this`",
    ]:
        [local_ref, *_] = children
        env0.ensure_expr_is_of_type(local_ref, T_grammar_symbol_)
        return (env0, env0)

    # ------------------------
    # relating to Environment Record bindings:

    elif p in [
        r"{CONDITION_1} : {var} does not already have a binding for {var}",
        r"{CONDITION_1} : {var} does not have a binding for {var}",
        r"{CONDITION_1} : {var} has a binding for the name that is the value of {var}",
        r"{CONDITION_1} : {var} has a binding for {var}",
        r"{CONDITION_1} : {var} must have an uninitialized binding for {var}",
    ]:
        [er_var, n_var] = children
        env0.assert_expr_is_of_type(er_var, T_Environment_Record)
        env0.assert_expr_is_of_type(n_var, T_String)
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : the binding for {var} in {var} cannot be deleted",
        r"{CONDITION_1} : the binding for {var} in {var} has not yet been initialized",
        r"{CONDITION_1} : the binding for {var} in {var} is a mutable binding",
        r"{CONDITION_1} : the binding for {var} in {var} is a strict binding",
        r"{CONDITION_1} : the binding for {var} in {var} is an uninitialized binding",
    ]:
        [n_var, er_var] = children
        env0.assert_expr_is_of_type(n_var, T_String)
        env0.assert_expr_is_of_type(er_var, T_Environment_Record)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the binding for {var} is an indirect binding":
        # todo: make ER explicit in spec?
        [n_var] = children
        env0.assert_expr_is_of_type(n_var, T_String)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the binding exists":
        # elliptical
        [] = children
        return (env0, env0)

    elif p == r'{CONDITION_1} : When {SETTABLE} is instantiated, it will have a direct binding for {var}':
        [settable, var] = children
        env0.assert_expr_is_of_type(settable, T_Environment_Record | T_empty_)
        env0.assert_expr_is_of_type(var, T_String)
        return (env0, env0)

    # --------------------------------------------------
    # relating to strict code:

    elif p in [
        r"{CONDITION_1} : the source text matched by {PROD_REF} is contained in strict mode code",
        r"{CONDITION_1} : the source text matched by {PROD_REF} is strict mode code",
        r"{CONDITION_1} : the source text matched by {var} is non-strict code",
    ]:
        [prod_ref] = children
        env0.assert_expr_is_of_type(prod_ref, T_Parse_Node)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the source text matched by the syntactic production that is being evaluated is contained in strict mode code":
        [] = children
        return (env0, env0)

    # -------------------------------------------------
    # introduce metavariable:

    elif p == r"{CONDITION_1} : {DOTTING} contains a Record {var} such that {CONDITION_1}":
        [ex, var, cond] = children
        (ex_t, env1) = tc_expr(ex, env0); assert env1 is env0
        assert ex_t.is_a_subtype_of_or_equal_to(T_List)
        assert ex_t.element_type.is_a_subtype_of_or_equal_to(T_Record)
        env_for_cond = env0.plus_new_entry(var, ex_t.element_type)
        (cond_t_env, cond_f_env) = tc_cond(cond, env_for_cond)
        return (cond_t_env, env0)

    elif p == r"{CONDITION_1} : there does not exist an element {var} of {var} such that {CONDITION_1}":
        [member_var, list_var, cond] = children
        env1 = env0.ensure_expr_is_of_type(list_var, ListType(T_String)) # over-specific
        env2 = env1.plus_new_entry(member_var, T_String)
        (t_env, f_env) = tc_cond(cond, env2)
        return (env1, env1)

    elif p in [
        r'{CONDITION_1} : there does not exist a member {var} of {var} such that {CONDITION_1}',
        r'{CONDITION_1} : there exists a member {var} of {var} such that {CONDITION_1}',
    ]:
        [member_var, set_var, cond] = children
        env1 = env0.ensure_expr_is_of_type(set_var, T_CharSet)
        env2 = env1.plus_new_entry(member_var, T_character_)
        (t_env, f_env) = tc_cond(cond, env2)
        assert t_env is f_env
        return (env1, env1)

    elif p == r"{CONDITION_1} : there exists an integer {var} between 0 (inclusive) and {var} (exclusive) such that {CONDITION_1}":
        [i_var, m_var, cond] = children
        env0.assert_expr_is_of_type(m_var, T_MathInteger_)
        env_for_cond = env0.plus_new_entry(i_var, T_MathInteger_)
        return tc_cond(cond, env_for_cond)

    elif p == r"{CONDITION_1} : there exists a WriteSharedMemory or ReadModifyWriteSharedMemory event {var} that has {var} in its range such that {CONDITION_1}":
        [let_var, i, cond] = children
        env0.assert_expr_is_of_type(i, T_MathInteger_)
        env_for_cond = env0.plus_new_entry(let_var, T_WriteSharedMemory_event | T_ReadModifyWriteSharedMemory_event)
        return tc_cond(cond, env_for_cond)

    elif p == r"{CONDITION_1} : there exists an event {var} such that {CONDITION}":
        [let_var, cond] = children
        env_for_cond = env0.plus_new_entry(let_var, T_Shared_Data_Block_event)
        return tc_cond(cond, env_for_cond)

    elif p == r"{CONDITION_1} : {SETTABLE} &ne; {SETTABLE} for any integer value {var} in the range {LITERAL} through {var}, exclusive":
        [seta, setb, let_var, lo, hi] = children
        env0.assert_expr_is_of_type(lo, T_MathInteger_)
        env0.assert_expr_is_of_type(hi, T_MathInteger_)
        env_for_settables = env0.plus_new_entry(let_var, T_MathInteger_)
        env_for_settables.assert_expr_is_of_type(seta, T_MathInteger_)
        env_for_settables.assert_expr_is_of_type(setb, T_MathInteger_)
        return (env0, env0)

    # --------------------------------------------------
    # whatever

    elif p == r'{CONDITION_1} : {var} is the same Number value as {var}':
        [var1, var2] = children
        env0.assert_expr_is_of_type(var1, T_Number)
        env1 = env0.ensure_expr_is_of_type(var2, T_Number)
        return (env1, env1)

    elif p == r'{CONDITION_1} : {var} is the same sequence of code units as {var}':
        [var1, var2] = children
        env0.assert_expr_is_of_type(var1, T_String)
        env0.ensure_expr_is_of_type(var2, T_String)
        return (env0, env0)

    elif p == r'{NUM_COMPARISON} : {NUM_COMPARAND} {NUM_COMPARATOR} {NUM_COMPARAND} {NUM_COMPARATOR} {NUM_COMPARAND}':
        [a, _, b, _, c] = children
        env0.assert_expr_is_of_type(a, T_MathInteger_)
        env1 = env0.ensure_expr_is_of_type(b, T_MathInteger_ | T_MathNegInfinity_ | T_MathPosInfinity_)
        env0.assert_expr_is_of_type(c, T_MathInteger_)
        env2 = env1.with_expr_type_narrowed(b, T_MathInteger_)
        return (env2, env2)

    elif p in [
        r"{NUM_COMPARISON} : {NUM_COMPARAND} {NUM_COMPARATOR} {NUM_COMPARAND}",
    ]:
        [a, op, b] = children
        (a_t, env1) = tc_expr(a, env0);
        (b_t, env2) = tc_expr(b, env1);

        if a_t.is_a_subtype_of_or_equal_to(T_ExtendedMathReal_) and b_t.is_a_subtype_of_or_equal_to(T_ExtendedMathReal_):
            # great!

            # XXX: `_x_ &lt; Y` excludes _x_ being +&infin;
            # kludge:
            if op.source_text() in ['&lt;', 'is less than', '&le;'] and b.source_text() == '0':
                (is_t,   _) = a_t.split_by(T_MathReal_ | T_MathNegInfinity_)
                (isnt_t, _) = a_t.split_by(T_MathReal_ | T_MathPosInfinity_)
                return (
                    env2.with_expr_type_narrowed(a, is_t),
                    env2.with_expr_type_narrowed(a, isnt_t)
                )

        elif a_t.is_a_subtype_of_or_equal_to(T_BigInt) and b_t.is_a_subtype_of_or_equal_to(T_BigInt):
            # great!
            pass

        elif (a_t.is_a_subtype_of_or_equal_to(T_Number) and b_t.is_a_subtype_of_or_equal_to(T_Number)):
            # Probably good, except for NaN

            if (
                T_NaN_Number_.is_a_subtype_of_or_equal_to(a_t)
                or
                T_NaN_Number_.is_a_subtype_of_or_equal_to(b_t)
            ):
                add_pass_error(
                    cond,
                    "possible comparison involving NaN"
                )

            if op.source_text() in ['=', '&ne;']:
                add_pass_error(
                    cond,
                    "We avoid Number comparisons involving = or &ne;"
                )

        else:
            add_pass_error(
                cond,
                f"comparison has incompatible types: {a_t} vs. {b_t}"
            )
        return (env2, env2)

    elif p == r'{CONDITION_1} : the file {h_a} of the Unicode Character Database provides a simple or common case folding mapping for {var}':
        [h_a, var] = children
        assert h_a.source_text() == '<a href="https://unicode.org/Public/UCD/latest/ucd/CaseFolding.txt"><code>CaseFolding.txt</code></a>'
        env1 = env0.ensure_expr_is_of_type(var, T_character_)
        return (env1, env1)

    elif p == r'{CONDITION_1} : {var} does not consist of a single code unit':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_String)
        return (env1, env1)

    elif p == r'{CONDITION_1} : {var} does not contain exactly one character':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_CharSet)
        return (env1, env1)

    elif p == r'{CONDITION_1} : the Directive Prologue of {PROD_REF} contains a Use Strict Directive':
        [prod_ref] = children
        # XXX check that prod_ref makes sense
        return (env0, env0)

    elif p == r'{CONDITION_1} : The surrounding agent is not in the critical section for any WaiterList':
        # nothing to check
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : The execution context stack has at least two elements",
        r"{CONDITION_1} : The execution context stack is not empty",
        r"{CONDITION_1} : the execution context stack is empty",
    ]:
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : When we return here, {var} has already been removed from the execution context stack and {var} is the currently running execution context":
        [a_var, b_var] = children
        env0.assert_expr_is_of_type(a_var, T_execution_context)
        env0.assert_expr_is_of_type(b_var, T_execution_context)
        return (env0, env0)

    elif p == r'{CONDITION_1} : no such execution context exists':
        [] = children
        return (env0, env0)

    elif p == r'{CONDITION_1} : The surrounding agent is in the critical section for {var}':
        [var] = children
        env0.assert_expr_is_of_type(var, T_WaiterList)
        return (env0, env0)

    elif p in [
        r'{CONDITION_1} : {EX} is an element of {var}',
        r"{CONDITION_1} : {EX} is not an element of {var}",
    ]:
        [value_ex, list_var] = children
        env1 = env0.ensure_A_can_be_element_of_list_B(value_ex, list_var)
        return (env1, env1)

    elif p in [
        r"{CONDITION_1} : {SETTABLE} contains {EX}",
        r"{CONDITION_1} : {EX} does not contain {EX}",
    ]:
        [list_var, value_var] = children
        env1 = env0.ensure_A_can_be_element_of_list_B(value_var, list_var)
        return (env1, env1)

    elif p == r"{CONDITION_1} : {var} is not in {PREFIX_PAREN}":
        [item_var, set_pp] = children
        env0.assert_expr_is_of_type(set_pp, T_Set)
        env0.assert_expr_is_of_type(item_var, T_event_)
        return (env0, env0)

    elif p == r'{CONDITION_1} : {var} has a numeric value less than {code_unit_lit}':
        [var, code_unit_lit] = children
        env1 = env0.ensure_expr_is_of_type(var, T_code_point_) # odd
        return (env1, env1)

    elif p in [
        r"{CONDITION_1} : {EX} is different from {EX}",
        r"{CONDITION_1} : {EX} is the same as {EX}",
        r"{CONDITION_1} : {var} is not the same as {var}",
        r"{CONDITION_1} : {EX} is not the same value as {var}",
        r"{CONDITION_1} : {EX} is {PREFIX_PAREN}",
    ]:
        [exa, exb] = children
        (exa_type, exa_env) = tc_expr(exa, env0); assert exa_env is env0
        (exb_type, exb_env) = tc_expr(exb, env0); assert exb_env is env0
        if exa_type == exb_type:
            # good
            env1 = env0
        elif exa_type == T_TBD:
            env1 = env0.with_expr_type_replaced(exa, exb_type)
        elif exb_type == T_TBD:
            env1 = env0.with_expr_type_replaced(exb, exa_type)
        elif exa_type == T_Declarative_Environment_Record and exb_type == T_Environment_Record:
            env1 = env0.with_expr_type_narrowed(exb, exa_type)
        elif exa_type.is_a_subtype_of_or_equal_to(T_Number) and exb_type.is_a_subtype_of_or_equal_to(T_Number):
            env1 = env0
        else:
            assert 0, (exa_type, exb_type)
        return (env1, env1)

    elif p == r'{CONDITION_1} : {var} and {var} are exactly the same sequence of code units (same length and same code units at corresponding indices)':
        # occurs once, in SameValueNonNumber
        [vara, varb] = children
        enva = env0.ensure_expr_is_of_type(vara, T_String); assert enva is env0
        envb = env0.ensure_expr_is_of_type(varb, T_String); # assert envb is env0
        return (envb, envb)

    elif p == r'{CONDITION_1} : {EX} and {EX} are both {LITERAL} or both {LITERAL}':
        # occurs once, in SameValueNonNumber
        [exa, exb, litc, litd] = children
        assert litc.source_text() == '*true*'
        assert litd.source_text() == '*false*'
        enva = env0.ensure_expr_is_of_type(exa, T_Boolean); assert enva is env0
        envb = env0.ensure_expr_is_of_type(exb, T_Boolean); # assert envb is env0
        return (envb, envb)

    elif p == r'{CONDITION_1} : {var} and {var} are both the same Symbol value':
        # occurs once, in SameValueNonNumber
        [vara, varb] = children
        enva = env0.ensure_expr_is_of_type(vara, T_Symbol); assert enva is env0
        envb = env0.ensure_expr_is_of_type(varb, T_Symbol); # assert envb is env0
        return (envb, envb)

    elif p == r'{CONDITION_1} : {var} and {var} are the same Number value':
        # in Abstract Relational Comparison
        [vara, varb] = children
        enva = env0.ensure_expr_is_of_type(vara, T_Number); # assert enva is env0
        envb = enva.ensure_expr_is_of_type(varb, T_Number); # assert envb is env0
        return (envb, envb)

    elif p == r'{CONDITION_1} : {var} and {var} are the same Object value':
        # in SameValueNonNumber
        [vara, varb] = children
        enva = env0.ensure_expr_is_of_type(vara, T_Object); # assert enva is env0
        envb = enva.ensure_expr_is_of_type(varb, T_Object); # assert envb is env0
        return (envb, envb)

    elif p == r"{CONDITION_1} : {EX} and {EX} are the same Shared Data Block values":
        [exa, exb] = children
        env1 = env0.ensure_expr_is_of_type(exa, T_Shared_Data_Block)
        env2 = env1.ensure_expr_is_of_type(exb, T_Shared_Data_Block)
        return (env2, env2)

    elif p in [
        r"{CONDITION_1} : {var} and {var} are the same Module Record",
        r"{CONDITION_1} : {var} and {DOTTING} are the same Module Record",
        r"{CONDITION_1} : {DOTTING} and {DOTTING} are not the same Module Record",
    ]:
        [ex1, ex2] = children
        env0.assert_expr_is_of_type(ex1, T_Module_Record)
        env0.assert_expr_is_of_type(ex2, T_Module_Record)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {EX} is the same Parse Node as {EX}":
        [exa, exb] = children
        env0.assert_expr_is_of_type(exa, T_Parse_Node)
        env0.assert_expr_is_of_type(exb, T_Parse_Node)
        return (env0, env0)

    elif p == r'{CONDITION_1} : {var} has attribute values { {DSBN}: *true*, {DSBN}: *true* }':
        [var, dsbn1, dsbn2] = children
        env1 = env0.ensure_expr_is_of_type(var, T_Property_Descriptor)
        assert dsbn1.source_text() == '[[Writable]]'
        assert dsbn2.source_text() == '[[Enumerable]]'
        return (env1, env1)

    elif p in [
        r'{CONDITION_1} : {EX} is {var}',
        r"{CONDITION_1} : {EX} is the same value as {EX}",
    ]:
        [a_ex, b_ex] = children
        (a_t, a_env) = tc_expr(a_ex, env0)
        (b_t, b_env) = tc_expr(b_ex, env0); assert b_env is env0
        assert a_t != T_TBD
        if b_t == T_TBD:
            env1 = env0.with_expr_type_replaced(b_ex, a_t)
        else:
            # assert a_t.is_a_subtype_of_or_equal_to(b_t)
            (common_t, _) = a_t.split_by(b_t)
            assert common_t != T_0
            env1 = env0
        e = env_or(a_env, env0)
        return (e, e)

    elif p == r'{CONDITION_1} : {var} has {var} in its range':
        [sdbe_var, loc_var] = children
        env1 = env0.ensure_expr_is_of_type(sdbe_var, T_Shared_Data_Block_event)
        env2 = env1.ensure_expr_is_of_type(loc_var, T_MathInteger_)
        return (env2, env2)

    elif p in [
        r'{CONDITION_1} : {EX} is in {EX}',
        r'{CONDITION_1} : {var} is not in {var}',
        r'{CONDITION_1} : {var} occurs exactly once in {var}',
    ]:
        [item_var, container_var] = children
        (container_t, env1) = tc_expr(container_var, env0); assert env1 is env0
        if container_t == T_String:
            env0.assert_expr_is_of_type(item_var, T_code_unit_)
        elif container_t == T_CharSet:
            env0.assert_expr_is_of_type(item_var, T_character_)
        elif container_t == T_Relation:
            env0.assert_expr_is_of_type(item_var, T_event_pair_)
        elif isinstance(container_t, ListType):
            el_type = container_t.element_type
            if el_type == T_Cyclic_Module_Record:
                # The stack only contains CMRs,
                # but _requiredModule_ might be a non-C MR:
                env0.assert_expr_is_of_type(item_var, T_Module_Record)
                # It's still reasonable to ask if _requiredModule_ is in the stack.
            else:
                assert 0, container_t
        else:
            assert 0, container_t
        return (env0, env0)

    elif p == r'{CONDITION_1} : There are sufficient bytes in {var} starting at {var} to represent a value of {var}':
        [ab_var, st_var, t_var] = children
        env0.assert_expr_is_of_type(ab_var, T_ArrayBuffer_object_ | T_SharedArrayBuffer_object_)
        env0.assert_expr_is_of_type(st_var, T_MathInteger_)
        env0.assert_expr_is_of_type(t_var, T_TypedArray_element_type_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : The next step never returns an abrupt completion because {CONDITION_1}":
        [subcond] = children
        return tc_cond(subcond, env0, asserting)

    elif p == r'{CONDITION_1} : {var} does not have an own property with key {var}':
        [obj_var, key_var] = children
        env0.assert_expr_is_of_type(obj_var, T_Object)
        env0.assert_expr_is_of_type(key_var, T_String | T_Symbol)
        return (env0, env0)

    elif p == r'{CONDITION_1} : {var} is not already suspended':
        [var] = children
        env0.assert_expr_is_of_type(var, T_execution_context)
        return (env0, env0)

    elif p == r'{CONDITION_1} : {var} is on the list of waiters in {var}':
        [w_var, wl_var] = children
        env0.assert_expr_is_of_type(w_var, T_agent_signifier_)
        env0.assert_expr_is_of_type(wl_var, T_WaiterList)
        return (env0, env0)

    elif p == r'{CONDITION_1} : {var} was notified explicitly by another agent calling NotifyWaiter with arguments {var} and {var}':
        [w_var, *blah] = children
        env0.assert_expr_is_of_type(w_var, T_agent_signifier_)
        return (env0, env0)

    elif p == r'{CONDITION_1} : {var} is as small as possible':
        [var] = children
        env0.assert_expr_is_of_type(var, T_MathInteger_)
        return (env0, env0)

    elif p == r'{CONDITION_1} : {var} is odd':
        [var] = children
        env0.assert_expr_is_of_type(var, T_MathInteger_)
        return (env0, env0)

    elif p == r'{CONDITION_1} : {PROD_REF} is `export` {nonterminal}':
        [prod_ref, nont] = children
        return (env0, env0)

    elif p in [
        r'{CONDITION_1} : {EX} is empty',
        r"{CONDITION_1} : {var} is not empty",
    ]:
        [var] = children
        env0.assert_expr_is_of_type(var, T_CharSet | T_List | T_String)
        # XXX For String, change spec to "is [not] the empty String" ?
        return (env0, env0)

    elif p == r"{CONDITION_1} : {NAMED_OPERATION_INVOCATION} is not empty":
        [noi] = children
        env0.assert_expr_is_of_type(noi, T_List)
        return (env0, env0)

    elif p == r"{CONDITION_1} : We've reached the starting point of an `export *` circularity":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} provides the direct binding for this export":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Source_Text_Module_Record)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} imports a specific binding for this export":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Source_Text_Module_Record)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is not contained within an? {nonterminal}, {nonterminal}, or {nonterminal}":
        [var, *nont_] = children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is the {nonterminal} of an? {nonterminal}":
        [var, nont1, nont2] = children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : {EX} is -1",
        r"{CONDITION_1} : {EX} is not -1",
    ]:
        [ex] = children
        env0.assert_expr_is_of_type(ex, T_MathInteger_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {DOTTING} is not the ordinary object internal method defined in {h_emu_xref}":
        [dotting, emu_xref] = children
        env0.assert_expr_is_of_type(dotting, T_proc_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : This is a circular import request":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : A `default` export was not explicitly defined by this module":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : There is more than one `*` import that includes the requested name":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} does not have any fields":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Property_Descriptor)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} does not include the element {LITERAL}":
        [list_var, item_lit] = children
        env1 = env0.ensure_expr_is_of_type(list_var, ListType(T_String))
        env0.assert_expr_is_of_type(item_lit, T_String)
        return (env1, env1)

    elif p == r"{CONDITION_1} : we return here":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : the async function either threw an exception or performed an implicit or explicit return; all awaiting is done":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : the async generator either threw an exception or performed either an implicit or explicit return":
        [] = children
        return (env0, env0)

    elif p == r"{TYPE_TEST} : Type({TYPE_ARG}) is not an element of {var}":
        # once, in CreateListFromArrayLike
        [type_arg, var] = children
        env0.assert_expr_is_of_type(var, ListType(T_LangTypeName_))
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} does not contain a rest parameter, any binding patterns, or any initializers. It may contain duplicate identifiers":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} has any elements":
        [var] = children
        env0.assert_expr_is_of_type(var, T_List)
        return (env0, env0)

    elif p == r"{CONDITION_1} : it must be in the Object Environment Record":
        # elliptical
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : The following loop will terminate":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} binds a single name":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : {var} contains any duplicate entries",
        r"{CONDITION_1} : {var} contains no duplicate entries",
        r"{CONDITION_1} : {var} has any duplicate entries",
        r"{CONDITION_1} : {var} has no duplicate entries",
    ]:
        [var] = children
        env0.assert_expr_is_of_type(var, T_List)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the generator either threw an exception or performed either an implicit or explicit return":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is this specification's name of an intrinsic object. The corresponding object must be an intrinsic that is intended to be used as the {DSBN} value of an object":
        [var, dsbn] = children
        env0.assert_expr_is_of_type(var, T_String)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} does not currently have a property {var}":
        [obj_var, pn_var] = children
        env0.assert_expr_is_of_type(obj_var, T_Object)
        env0.assert_expr_is_of_type(pn_var, T_String | T_Symbol)
        return (env0, env0)

    elif p == r'{CONDITION_1} : {var} contains any code unit other than *"d"*, *"g"*, *"i"*, *"m"*, *"s"*, *"u"*, or *"y"* or if it contains the same code unit more than once':
        [var] = children
        env0.assert_expr_is_of_type(var, T_String)
        return (env0, env0)

    elif p == r"{CONDITION_1} : This is an attempt to change the value of an immutable binding":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is now the running execution context":
        [var] = children
        env0.assert_expr_is_of_type(var, T_execution_context)
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : {PROD_REF} is the token `false`",
        r"{CONDITION_1} : {PROD_REF} is the token `true`",
    ]:
        [prod_ref] = children
        assert prod_ref.source_text() == '|BooleanLiteral|'
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} has no elements":
        [var] = children
        env0.assert_expr_is_of_type(var, T_List)
        return (env0, env0)

    elif p == r"{CONDITION_1} : an implementation-defined debugging facility is available and enabled":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} contains a formal parameter mapping for {var}":
        [avar, bvar] = children
        env0.assert_expr_is_of_type(avar, T_Object)
        env0.assert_expr_is_of_type(bvar, T_String | T_Symbol)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {DOTTING} exists and has been initialized":
        [dotting] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} and {var} are not the same Realm Record":
        [avar, bvar] = children
        env0.assert_expr_is_of_type(avar, T_Realm_Record)
        env0.assert_expr_is_of_type(bvar, T_Realm_Record)
        return (env0, env0)

    elif p == r"{CONDITION_1} : All named exports from {var} are resolvable":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Source_Text_Module_Record)
        return (env0, env0)

    elif p == r"{CONDITION_1} : Evaluate has already been invoked on {var} and successfully completed":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Module_Record)
        return (env0, env0)

    elif p == r'''{CONDITION_1} : The mathematical value of {var}'s {starred_str} property is {EX}''':
        [var, prop_name, ex] = children
        env0.assert_expr_is_of_type(var, T_Object)
        env0.assert_expr_is_of_type(ex, T_MathInteger_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} and {var} are finite and non-zero":
        [avar, bvar] = children
        env0.assert_expr_is_of_type(avar, T_Number)
        env0.assert_expr_is_of_type(bvar, T_Number)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the character {EX} is one of {nonterminal}":
        [ex, nonterminal] = children
        env0.assert_expr_is_of_type(ex, T_character_)
        assert nonterminal.source_text() == '|LineTerminator|'
        return (env0, env0)

    elif p == r"{CONDITION_1} : {PP_NAMED_OPERATION_INVOCATION} is not the same character value as {PP_NAMED_OPERATION_INVOCATION}":
        [anoi, bnoi] = children
        env0.assert_expr_is_of_type(anoi, T_character_)
        env0.assert_expr_is_of_type(bnoi, T_character_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is finite and is neither {NUM_LITERAL} nor {NUM_LITERAL}":
        [var, lita, litb] = children
        env1 = env0.ensure_expr_is_of_type(var, T_FiniteNumber_)
        env1.assert_expr_is_of_type(lita, T_FiniteNumber_)
        env1.assert_expr_is_of_type(litb, T_FiniteNumber_)
        return (env1, env1)

    elif p in [
        r"{CONDITION_1} : {var} is in the inclusive interval from {NUM_LITERAL} to {NUM_LITERAL}",
        r"{CONDITION_1} : {var} is not in the inclusive interval from {NUM_LITERAL} to {NUM_LITERAL}",
    ]:
        [var, lita, litb] = children
        env1 = env0.ensure_expr_is_of_type(var, T_MathInteger_)
        env1.assert_expr_is_of_type(lita, T_MathInteger_)
        env1.assert_expr_is_of_type(litb, T_MathInteger_)
        return (env1, env1)

    elif p == r"{CONDITION_1} : the host is a web browser":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : the host requires use of an exotic object to serve as {var}'s global object":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Realm_Record)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the host requires that the `this` binding in {var}'s global scope return an object other than the global object":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Realm_Record)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the code units at index ({SUM}) and ({SUM}) within {var} do not represent hexadecimal digits":
        [posa, posb, var] = children
        env0.assert_expr_is_of_type(posa, T_MathInteger_)
        env0.assert_expr_is_of_type(posb, T_MathInteger_)
        env0.assert_expr_is_of_type(var, T_String)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} does not contain a valid UTF-8 encoding of a Unicode code point":
        [var] = children
        env0.assert_expr_is_of_type(var, ListType(T_MathInteger_))
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} and {var} each contain exactly one character":
        [a,b] = children
        env0.assert_expr_is_of_type(a, T_CharSet)
        env0.assert_expr_is_of_type(b, T_CharSet)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} contains any {nonterminal}":
        [rvar, nonterminal] = children
        env0.assert_expr_is_of_type(rvar, T_Object)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} contains a single {nonterminal}":
        [var, nonterminal] = children    
        env0.assert_expr_is_of_type(var, ListType(T_Parse_Node))
        return (env0, env0)

    elif p == r"{CONDITION_1} : the {var}<sup>th</sup> capture of {var} was defined with a {nonterminal}":
        [ivar, rvar, nonterminal] = children
        env0.assert_expr_is_of_type(ivar, T_MathInteger_)
        env0.assert_expr_is_of_type(rvar, T_Object)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is a canonical, unaliased Unicode property name listed in the &ldquo;Canonical property name&rdquo; column of {h_emu_xref}":
        [v, emu_xref] = children
        env0.assert_expr_is_of_type(v, ListType(T_code_point_))
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is a property value or property value alias for the Unicode property {var} listed in {h_a}":
        [va, vb, h_a] = children
        env0.assert_expr_is_of_type(va, ListType(T_code_point_))
        env0.assert_expr_is_of_type(vb, ListType(T_code_point_))
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is a Unicode property name or property alias listed in the &ldquo;Property name and aliases&rdquo; column of {h_emu_xref}":
        [v, emu_xref] = children
        env0.assert_expr_is_of_type(v, ListType(T_code_point_))
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is a binary Unicode property or binary property alias listed in the &ldquo;Property name and aliases&rdquo; column of {h_emu_xref}":
        [v, emu_xref] = children
        env0.assert_expr_is_of_type(v, ListType(T_code_point_))
        return (env0, env0)

    elif p == r"{CONDITION_1} : {PP_NAMED_OPERATION_INVOCATION} is a Unicode property value or property value alias for the General_Category (gc) property listed in {h_a}":
        [noi, h_a] = children
        env0.assert_expr_is_of_type(noi, ListType(T_code_point_))
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} does not have a Generator component":
        [var] = children
        env0.assert_expr_is_of_type(var, T_execution_context)
        return (env0, env0)

    # ----

    elif p == r"{CONDITION_1} : {var} is not on the list of waiters in any WaiterList":
        [sig_var] = children
        env0.assert_expr_is_of_type(sig_var, T_agent_signifier_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is not on the list of waiters in {var}":
        [sig_var, wl_var] = children
        env0.assert_expr_is_of_type(sig_var, T_agent_signifier_)
        env0.assert_expr_is_of_type(wl_var, T_WaiterList)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {EX} and {EX} are valid byte offsets within the memory of {var}":
        [offset1, offset2, sdb] = children
        env1 = env0.ensure_expr_is_of_type(offset1, T_MathInteger_)
        env1.assert_expr_is_of_type(offset2, T_MathInteger_)
        env1.assert_expr_is_of_type(sdb, T_Shared_Data_Block)
        return (env1, env1)

    elif p == r"{CONDITION_1} : {var} is not one of {LITERAL}, {LITERAL}, {LITERAL}, or {LITERAL}":
        [var, *lit_] = children
        tc_expr
        (var_t, var_env) = tc_expr(var, env0); assert var_env is env0
        for lit in lit_:
            env0.assert_expr_is_of_type(lit, var_t)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} can be interpreted as an expansion of {nonterminal}":
        [var, nont] = children
        env0.assert_expr_is_of_type(var, T_String)
        return (env0, env0)

    elif p == r"{CONDITION_1} : neither {var} nor any prefix of {var} satisfies the syntax of a {nonterminal} (see {h_emu_xref})":
        [var1, var2, nont, emu_xref] = children
        assert same_source_text(var1, var2)
        env0.assert_expr_is_of_type(var1, T_String)
        return (env0, env0)

    elif p == r"{CONDITION_1} : GlobalSymbolRegistry does not currently contain an entry for {var}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_String | T_Symbol)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the first two code units of {var} are either {STR_LITERAL} or {STR_LITERAL}":
        [var, lita, litb] = children
        env0.assert_expr_is_of_type(var, T_String)
        env0.assert_expr_is_of_type(lita, T_String)
        env0.assert_expr_is_of_type(litb, T_String)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} contains a code unit that is not a radix-{var} digit":
        [svar, rvar] = children
        env0.assert_expr_is_of_type(svar, T_String)
        env0.assert_expr_is_of_type(rvar, T_MathInteger_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is the String value {STR_LITERAL}":
        [var, lit] = children
        env0.assert_expr_is_of_type(lit, T_String)
        env1 = env0.ensure_expr_is_of_type(var, T_Tangible_) # you'd expect T_String, but _hint_ in Date.prototype [ @@toPrimitive ]
        return (env1, env1)

    elif p == r"{CONDITION_1} : {var} starts with {STR_LITERAL}":
        [var, str_literal] = children
        env0.assert_expr_is_of_type(var, T_String)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} starts with {STR_LITERAL} followed by {EX} or more decimal digits":
        [var, str_literal, ex] = children
        env0.assert_expr_is_of_type(var, T_String)
        env0.assert_expr_is_of_type(ex, T_MathNonNegativeInteger_)
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : only one argument was passed",
    ]:
        [] = children
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : {var} is a non-negative integer which is &le; {EXPR}",
    ]:
        [a, b] = children
        env0.assert_expr_is_of_type(b, T_MathInteger_)
        env1 = env0.ensure_expr_is_of_type(a, T_MathInteger_)
        return (env1, env1)

    elif p == r"{CONDITION_1} : both {EX} and {EX} are {LITERAL}":
        [exa, exb, lit] = children
        (t, env1) = tc_expr(lit, env0); assert env1 is env0
        env1.assert_expr_is_of_type(exa, t)
        env1.assert_expr_is_of_type(exb, t)
        return (env1, env1)

    elif p == r"{CONDITION_1} : {var} is not currently an element of {var}":
        [item_var, list_var] = children
        env1 = env0.ensure_A_can_be_element_of_list_B(item_var, list_var)
        return (env1, env1)

    elif p == r"{NUM_COMPARISON} : {NUM_COMPARAND} is 10 or less":
        [x] = children
        env0.assert_expr_is_of_type(x, T_MathInteger_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {EX} is neither {LITERAL} nor the active function object":
        [ex, lit] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : When we reach this step, {var} has already been removed from the execution context stack and {var} is the currently running execution context":
        [vara, varb] = children
        env0.assert_expr_is_of_type(vara, T_execution_context)
        env0.assert_expr_is_of_type(varb, T_execution_context)
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : {var} has an? {DSBN} internal slot whose value is an Object",
    ]:
        [var, dsbn] = children
        env0.assert_expr_is_of_type(var, T_Object) # more specific?
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : the pairs {PAIR} and {PAIR} are in {EX}",
        r"{CONDITION_1} : the pairs {PAIR} and {PAIR} are not in {EX}",
        r"{CONDITION_1} : either {PAIR} or {PAIR} is in {EX}",
    ]:
        [paira, pairb, ex] = children
        env0.assert_expr_is_of_type(paira, T_event_pair_)
        env0.assert_expr_is_of_type(pairb, T_event_pair_)
        env0.assert_expr_is_of_type(ex, T_Relation)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} and {var} are in a race in {var}":
        [ea, eb, exe] = children
        env0.assert_expr_is_of_type(ea, T_Shared_Data_Block_event)
        env0.assert_expr_is_of_type(eb, T_Shared_Data_Block_event)
        env0.assert_expr_is_of_type(exe, T_candidate_execution)
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : {var} and {var} do not have disjoint ranges",
        r"{CONDITION_1} : {var} and {var} have equal ranges",
        r"{CONDITION_1} : {var} and {var} have overlapping ranges",
    ]:
        [ea, eb] = children
        env0.assert_expr_is_of_type(ea, T_Shared_Data_Block_event)
        env0.assert_expr_is_of_type(eb, T_Shared_Data_Block_event)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {EX} is not {var}":
        [ea, eb] = children
        # over-specific:
        env0.assert_expr_is_of_type(ea, T_Shared_Data_Block_event | T_host_defined_ | T_Undefined)
        env0.assert_expr_is_of_type(eb, T_Shared_Data_Block_event | T_host_defined_ | T_Undefined)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {EX} is listed in the &ldquo;Code Point&rdquo; column of {h_emu_xref}":
        [ex, emu_xref] = children
        env0.assert_expr_is_of_type(ex, T_code_point_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} has the same numeric value as a {h_emu_xref} or {h_emu_xref}":
        [var, emu_xref1, emu_xref2] = children
        env0.assert_expr_is_of_type(var, T_code_point_)
        return (env0, env0)

    # explicit-exotics:
    elif p in [
        r"{CONDITION_1} : the caller will not be overriding both {var}'s {DSBN} and {DSBN} essential internal methods",
        r"{CONDITION_1} : the caller will not be overriding all of {var}'s {DSBN}, {DSBN}, and {DSBN} essential internal methods",
    ]:
        var = children[0]
        env0.assert_expr_is_of_type(var, T_Object)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} contains a {nonterminal}":
        [var, nont] = children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        env0.assert_expr_is_of_type(nont, T_grammar_symbol_)
        return (env0, env0)

    # PR ? function-strictness
    elif p == r"{CONDITION_1} : the source text matched by {var} is strict mode code":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is not a {h_emu_xref} or {h_emu_xref}":
        [var, xrefa, xrefb] = children
        assert xrefa.source_text() == '<emu-xref href="#leading-surrogate"></emu-xref>'
        assert xrefb.source_text() == '<emu-xref href="#trailing-surrogate"></emu-xref>'
        env0.assert_expr_is_of_type(var, T_code_unit_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} or {var} is {LITERAL}":
        [v1, v2, lit] = children
        env0.assert_expr_is_of_type(v1, T_Number|T_BigInt)
        env0.assert_expr_is_of_type(v2, T_Number|T_BigInt)
        env0.assert_expr_is_of_type(lit, T_Number)
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : {LOCAL_REF} is {backticked_oth}",
    ]:
        [prod_ref, oth] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} has a Synchronize event":
        [var] = children
        env0.assert_expr_is_of_type(var, T_WaiterList)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} does not provide the direct binding for this export":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Module_Record)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {PP_NAMED_OPERATION_INVOCATION} contains any code points other than {backticked_word}, {backticked_word}, {backticked_word}, {backticked_word}, {backticked_word}, {backticked_word}, or {backticked_word}, or if it contains the same code point more than once":
        [noi, *bw_] = children
        env0.assert_expr_is_of_type(noi, T_Unicode_code_points_)
        for bw in bw_:
            assert len(bw.source_text()) == 3 # single-character 'words'
        return (env0, env0)

    elif p == r"{CONDITION_1} : {PP_NAMED_OPERATION_INVOCATION} contains {backticked_word}":
        [noi, bw] = children
        env0.assert_expr_is_of_type(noi, T_Unicode_code_points_)
        assert len(bw.source_text()) == 3 # single-character 'word'
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} has all of the internal slots of a For-In Iterator Instance ({h_emu_xref})":
        [var, emu_xref] = children
        env0.assert_expr_is_of_type(var, T_Object)
        return (env0, env0)

    elif p == r"{CONDITION_1} : This call to Evaluate is not happening at the same time as another call to Evaluate within the surrounding agent":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} and {var} have the same number of elements":
        [vara, varb] = children
        env0.assert_expr_is_of_type(vara, T_List)
        env0.assert_expr_is_of_type(varb, T_List)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} and {var} do not have the same number of elements":
        [vara, varb] = children
        env0.assert_expr_is_of_type(vara, T_List)
        env0.assert_expr_is_of_type(varb, T_List)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var}, {var}, and {var} have the same number of elements":
        [vara, varb, varc] = children
        env0.assert_expr_is_of_type(vara, T_List)
        env0.assert_expr_is_of_type(varb, T_List)
        env0.assert_expr_is_of_type(varc, T_List)
        return (env0, env0)

    elif p == r"{NUM_COMPARISON} : {NUM_COMPARAND} is equivalent to {NUM_COMPARAND}":
        [a, b] = children
        env0.assert_expr_is_of_type(a, T_agent_signifier_)
        env0.assert_expr_is_of_type(b, T_agent_signifier_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : The length of {var} is {var}":
        [list_var, len_var] = children
        env0.assert_expr_is_of_type(list_var, T_List)
        env0.assert_expr_is_of_type(len_var, T_MathNonNegativeInteger_)
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : {var} is an integral Number",
        r"{CONDITION_1} : {var} is not an integral Number",
        r"{CONDITION_1} : {var} is an odd integral Number",
    ]:
        [var] = children
        env0.assert_expr_is_of_type(var, T_Number)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the parse succeeded and no early errors were found":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is an instance of {var}":
        [var1, var2] = children
        env0.assert_expr_is_of_type(var1, T_Parse_Node)
        env0.assert_expr_is_of_type(var2, T_grammar_symbol_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is an instance of a nonterminal":
        [var1] = children
        env0.assert_expr_is_of_type(var1, T_Parse_Node)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {NAMED_OPERATION_INVOCATION} is not some Unicode code point matched by the {nonterminal} lexical grammar production":
        [noi, nont] = children
        env0.assert_expr_is_of_type(noi, T_code_point_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the goal symbol of the syntactic grammar is {nonterminal}":
        [nont] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : the syntactic goal symbol is not {nonterminal}":
        [nont] = children
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : {PROD_REF} has an? <sub>[{cap_word}]</sub> parameter",
    ]:
        [prod_ref, cap_word] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : the <sub>[Tagged]</sub> parameter was not set":
        [] = children
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : {NAMED_OPERATION_INVOCATION} is one of: {starred_str}, {starred_str}, {starred_str}, {starred_str}, {starred_str}, {starred_str}, {starred_str}, or {starred_str}",
        r"{CONDITION_1} : {NAMED_OPERATION_INVOCATION} is: {starred_str}, {starred_str}, {starred_str}, {starred_str}, {starred_str}, {starred_str}, {starred_str}, {starred_str}, or {starred_str}",
    ]:
        [noi, *ss_] = children
        env0.assert_expr_is_of_type(noi, T_String)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {NAMED_OPERATION_INVOCATION} is the same String value as the StringValue of any |ReservedWord| except for `yield` or `await`":
        [noi] = children
        env0.assert_expr_is_of_type(noi, T_String)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the number of elements in the result of {NAMED_OPERATION_INVOCATION} is greater than 2<sup>32</sup> - 1":
        [noi] = children
        env0.assert_expr_is_of_type(noi, T_List)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {LOCAL_REF} is contained in strict mode code":
        [local_ref] = children
        env0.assert_expr_is_of_type(local_ref, T_Parse_Node)
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : any source text is matched by this production",
    ]:
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : {LOCAL_REF} Contains {G_SYM}":
        [local_ref, g_sym] = children
        env0.assert_expr_is_of_type(local_ref, T_Parse_Node)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {LOCAL_REF} is {h_emu_grammar}":
        [local_ref, h_emu_grammar] = children
        env0.assert_expr_is_of_type(local_ref, T_Parse_Node)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {LOCAL_REF} is {h_emu_grammar}, {h_emu_grammar}, {h_emu_grammar}, {h_emu_grammar}, or {h_emu_grammar}":
        [local_ref, *h_emu_grammar_] = children
        env0.assert_expr_is_of_type(local_ref, T_Parse_Node)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {NAMED_OPERATION_INVOCATION} is a {nonterminal}":
        [noi, nont] = children
        # env0.assert_expr_is_of_type(noi, T_Parse_Node)
        assert nont.source_text() == '|ReservedWord|'
        # This isn't asking if {noi} is a Parse Node that is an instance of |ReservedWord|.
        # Rather, it's asking if {noi} is a String that could match |ReservedWord|.
        env0.assert_expr_is_of_type(noi, T_String)
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : {NAMED_OPERATION_INVOCATION} contains any duplicate entries",
        r"{CONDITION_1} : {NAMED_OPERATION_INVOCATION} contains any duplicate elements",
    ]:
        [noi] = children
        env0.assert_expr_is_of_type(noi, T_List)
        return (env0, env0)

    elif p == r"{CONDITION_1} : any element of {NAMED_OPERATION_INVOCATION} also occurs in {NAMED_OPERATION_INVOCATION}":
        [noi1, noi2] = children
        env0.assert_expr_is_of_type(noi1, T_List)
        env0.assert_expr_is_of_type(noi2, T_List)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {NAMED_OPERATION_INVOCATION} contains {starred_str}":
        [noi, ss] = children
        env0.assert_expr_is_of_type(noi, ListType(T_String))
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : {NAMED_OPERATION_INVOCATION} contains more than one occurrence of {starred_str}",
    ]:
        [noi, ss] = children
        env1 = env0.ensure_expr_is_of_type(noi, ListType(T_String))
        return (env1, env1)

    elif p == r"{CONDITION_1} : {NAMED_OPERATION_INVOCATION} contains any duplicate entries for {starred_str} and at least two of those entries were obtained from productions of the form {h_emu_grammar}":
        [noi, ss, emu_grammar] = children
        env1 = env0.ensure_expr_is_of_type(noi, ListType(T_String))
        return (env1, env1)

    elif p == r"{CONDITION_1} : {NAMED_OPERATION_INVOCATION} contains any {nonterminal}s":
        [noi, nont] = children
        env0.assert_expr_is_of_type(noi, ListType(T_Parse_Node))
        return (env0, env0)

    elif p == r"{CONDITION_1} : {LOCAL_REF} is not nested, directly or indirectly (but not crossing function or `static` initialization block boundaries), within an {nonterminal}":
        [local_ref, nont] = children
        env0.assert_expr_is_of_type(local_ref, T_Parse_Node)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {LOCAL_REF} is not nested, directly or indirectly (but not crossing function or `static` initialization block boundaries), within an {nonterminal} or a {nonterminal}":
        [local_ref, nonta, nontb] = children
        env0.assert_expr_is_of_type(local_ref, T_Parse_Node)
        return (env0, env0)

    elif p in [
        r"{CONDITION} : {CONDITION_1} unless {CONDITION_1}",
        r"{CONDITION} : {CONDITION_1}, unless {CONDITION_1}",
    ]:
        [conda, condb] = children
        tc_cond(conda, env0)
        tc_cond(condb, env0)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the source text containing {G_SYM} is eval code that is being processed by a direct eval":
        [g_sym] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : any element of {NAMED_OPERATION_INVOCATION} does not also occur in either {NAMED_OPERATION_INVOCATION}, or {NAMED_OPERATION_INVOCATION}":
        [noia, noib, noic] = children
        env0.assert_expr_is_of_type(noia, T_List)
        env0.assert_expr_is_of_type(noib, T_List)
        env0.assert_expr_is_of_type(noic, T_List)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {LOCAL_REF} contains two or more {nonterminal}s for which {NAMED_OPERATION_INVOCATION} is the same":
        [local_ref, nonta, noi] = children
        env0.assert_expr_is_of_type(local_ref, T_Parse_Node)
        # XXX noi
        return (env0, env0)

    elif p == r"{CONDITION_1} : {NAMED_OPERATION_INVOCATION} is larger than {NAMED_OPERATION_INVOCATION}":
        [noia, noib] = children
        env0.assert_expr_is_of_type(noia, T_MathInteger_)
        env0.assert_expr_is_of_type(noib, T_MathInteger_)
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : {PROD_REF} is contained within a {nonterminal} that is being parsed for JSON.parse (see step {h_emu_xref} of {h_emu_xref})",
        r"{CONDITION_1} : {PROD_REF} is contained within a {nonterminal} that is being evaluated for JSON.parse (see step {h_emu_xref} of {h_emu_xref})",
    ]:
        [prod_ref, nont, step_xref, alg_xref] = children
        env0.assert_expr_is_of_type(prod_ref, T_Parse_Node)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {NAMED_OPERATION_INVOCATION} is not matched by the {nonterminal} lexical grammar production":
        [noi, nont] = children
        env0.assert_expr_is_of_type(noi, T_code_point_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {NAMED_OPERATION_INVOCATION} is not the numeric value of some code point matched by the {nonterminal} lexical grammar production":
        [noi, nont] = children
        env0.assert_expr_is_of_type(noi, T_MathInteger_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the source text matched by {PROD_REF} is not a Unicode property name or property alias listed in the &ldquo;Property name and aliases&rdquo; column of {h_emu_xref}":
        [prod_ref, h_emu_xref] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : the source text matched by {PROD_REF} is not a Unicode property value or property value alias for the General_Category (gc) property listed in {h_a}, nor a binary property or binary property alias listed in the &ldquo;Property name and aliases&rdquo; column of {h_emu_xref}":
        [prod_ref, h_a, h_emu_xref] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : the source text matched by {PROD_REF} is not a property value or property value alias for the Unicode property or property alias given by the source text matched by {PROD_REF} listed in {h_a}":
        [prod_refa, prod_refb, h_a] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : the name is used once for a getter and once for a setter and in no other entries, and the getter and setter are either both static or both non-static":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : {EX} contains a PrivateElement whose {dsb_word} is {var}":
        [ex, dsb_word, var] = children
        env0.assert_expr_is_of_type(ex, ListType(T_PrivateElement))
        assert dsb_word.source_text() == '[[Key]]'
        env0.assert_expr_is_of_type(var, T_Private_Name)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} contains a PrivateElement whose {dsb_word} is {DOTTING}":
        [var, dsb_word, dotting] = children
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_PrivateElement))
        assert dsb_word.source_text() == '[[Key]]'
        env1.assert_expr_is_of_type(dotting, T_Private_Name)
        return (env1, env1)

    elif p == r"{CONDITION_1} : {EX} contains a Private Name whose {dsb_word} is {var}":
        [ex, dsb_word, var] = children
        env0.assert_expr_is_of_type(ex, ListType(T_Private_Name))
        assert dsb_word.source_text() == '[[Description]]'
        env0.assert_expr_is_of_type(var, T_String)
        return (env0, env0)

    elif p == r"{CONDITION_1} : Exactly one element of {var} is a Private Name whose {dsb_word} is {var}":
        [list_var, dsb_word, var] = children
        env0.assert_expr_is_of_type(list_var, ListType(T_Private_Name))
        assert dsb_word.source_text() == '[[Description]]'
        env0.assert_expr_is_of_type(var, T_String)
        return (env0, env0)

    elif p == r"{CONDITION_1} : This is only possible for getter/setter pairs":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is an instance of a production in {h_emu_xref}":
        [var, emu_xref] = children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} is the empty String (its length is 0)":
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_String)
        return (env1, env1)

    elif p == r"{CONDITION_1} : the decimal representation of {var} has 20 or fewer significant digits":
        [var] = children
        env0.assert_expr_is_of_type(var, T_MathReal_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : All elements of {var} have their {dsb_word} field set to {LITERAL}, {dsb_word} field set to {LITERAL}, and {dsb_word} field set to {LITERAL}":
        [var, dsb1, lit1, dsb2, lit2, dsb3, lit3] = children
        assert dsb1.source_text() == '[[AsyncEvaluation]]'
        assert dsb2.source_text() == '[[PendingAsyncDependencies]]'
        assert dsb3.source_text() == '[[EvaluationError]]'
        # could check that the lits have the right type.
        env0.assert_expr_is_of_type(var, ListType(T_Cyclic_Module_Record))
        return (env0, env0)

    elif p == r"{CONDITION_1} : {DOTTING} is {LITERAL} and was never previously set to {LITERAL}":
        [dotting, lita, litb] = children
        assert lita.source_text() == '*false*'
        assert litb.source_text() == '*true*'
        env0.assert_expr_is_of_type(dotting, T_Boolean)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} has been linked and declarations in its module environment have been instantiated":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Source_Text_Module_Record)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {EX} and {EX} are distinct values":
        [exa, exb] = children
        (exa_type, env1) = tc_expr(exa, env0)
        (exb_type, env2) = tc_expr(exb, env1)
        return (env2, env2)

    elif p == r"{CONDITION_1} : The current execution context will not subsequently be used for the evaluation of any ECMAScript code or built-in functions. The invocation of Call subsequent to the invocation of this abstract operation will create and push a new execution context before performing any such evaluation":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : The following Set will succeed, since formal parameters mapped by arguments objects are always writable":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : {var} has {EX} elements":
        [var, ex] = children
        env0.assert_expr_is_of_type(var, T_List)
        env0.assert_expr_is_of_type(ex, T_MathNonNegativeInteger_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {EX} is a non-negative integer less than or equal to {EX}":
        [exa, exb] = children
        env0.assert_expr_is_of_type(exa, T_MathNonNegativeInteger_)
        env0.assert_expr_is_of_type(exb, T_MathNonNegativeInteger_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {EX} is an integer between {EX} and {EX}, inclusive":
        [exa, exb, exc] = children
        env0.assert_expr_is_of_type(exa, T_MathInteger_)
        env0.assert_expr_is_of_type(exb, T_MathInteger_)
        env0.assert_expr_is_of_type(exc, T_MathInteger_)
        return (env0, env0)

    else:
        stderr()
        stderr("tc_cond:")
        stderr('    elif p == r"%s":' % p)
        sys.exit(0)

# ------------------------------------------------------------------------------

def tc_logical(logical_structure, env0, asserting):

    def appropriate_function(x):
        if isinstance(x, ANode):
            return tc_cond
        elif isinstance(x, tuple):
            return tc_logical
        else:
            assert 0

    assert isinstance(logical_structure, tuple)
    assert len(logical_structure) == 2
    (operator, operands) = logical_structure
    if operator == 'or':
        # Each cond is type-checked under the assumption that
        # all preceding conditions failed.
        t_envs = []
        f_env = env0
        for cond in operands:
            # If `asserting` is True, that only propagates to the last cond
            # (again, assuming that all previous conditions failed).
            sub_asserting = asserting if (cond is operands[-1]) else False
            (t_env, f_env) = appropriate_function(cond)(cond, f_env, sub_asserting)
            t_envs.append(t_env)
        return ( envs_or(t_envs), f_env )

    elif operator == 'and':
        # Each cond is type-checked under the assumption that
        # all preceding conditions succeeded.
        t_env = env0
        f_envs = []
        for cond in operands:
            (t_env, f_env) = appropriate_function(cond)(cond, t_env, asserting)
            f_envs.append(f_env)
        return ( t_env, envs_or(f_envs) )

    else:
        assert 0

# ------------------------------------------------------------------------------

def tc_expr(expr, env0, expr_value_will_be_discarded=False):
    p = str(expr.prod)
    expr_text = expr.source_text()

    if trace_this_op:
        print()
        print("Entering e:", p)
        print("           ", expr_text)
        mytrace(env0)

    if expr_text in env0.vars:
        if trace_this_op:
            print()
            print("Getting type from cache")
        expr_type = env0.vars[expr_text]
        # stderr("cache: %s :: %s" % (expr_text, expr_type))
        assert isinstance(expr_type, Type)
        env1 = env0

    else:
        (expr_type, env1) = tc_expr_(expr, env0, expr_value_will_be_discarded)

        assert isinstance(expr_type, Type)
        assert isinstance(env1, Env)

        if expr_type in [T_Top_, T_TBD, T_0]:
            add_pass_error(
                expr,
                "warning: expr `%s` has type %s" % (expr_text, expr_type)
            )

    if 0 and not expr_value_will_be_discarded:
        if expr_type != T_Top_ and T_not_returned.is_a_subtype_of_or_equal_to(expr_type):
            add_pass_error(
                expr,
                f"warning: `{p}` could be not_returned"
            )
            # There are a few problems with this:
            # - If a param's type isn't Top_, but has been carved down from Top_,
            #   it will probably include not_returned.
            #   (Mind you, there's a problem there anyway.)
            #
            # - Can't pass expr_value_will_be_discarded=True to assert_expr_is_of_type.
            #   (Only affects "Perform LeaveCriticalSection" step.)
            #
            # - In cases where it actually makes a useful complaint,
            #   it complains at multiple levels.
            #   (But that's okay, because you're going to fix it, right?)

    if trace_this_op:
        print()
        print("Leaving e:", p)
        print("          ", expr_text)
        print(" has type:", expr_type)
        mytrace(env1)

    return (expr_type, env1)

# --------------------

def tc_expr_(expr, env0, expr_value_will_be_discarded):
    p = str(expr.prod)
    children = expr.children

    # stderr('>>>', expr.source_text())

    if p in [
        r"{EXPR} : the result of {PP_NAMED_OPERATION_INVOCATION}",
        r"{EXPR} : {EX}",
        r"{EX} : ({EX})",
        r"{EX} : the value of {SETTABLE}",
        r"{EX} : the {var} flag",
        r"{EX} : {code_point_lit}",
        r"{EX} : {LITERAL}",
        r"{EX} : {LOCAL_REF}",
        r"{EX} : {NUM_EXPR}",
        r"{EX} : {PAIR}",
        r"{EX} : {PP_NAMED_OPERATION_INVOCATION}",
        r"{EX} : {RECORD_CONSTRUCTOR}",
        r"{FACTOR} : ({NUM_EXPR})",
        r"{FACTOR} : {NUM_LITERAL}",
        r"{FACTOR} : {PP_NAMED_OPERATION_INVOCATION}",
        r"{FACTOR} : {SETTABLE}",
        r"{LITERAL} : {code_unit_lit}",
        r"{LITERAL} : {NUM_LITERAL}",
        r"{LOCAL_REF} : {PROD_REF}",
        r"{LOCAL_REF} : {SETTABLE}",
        r"{NAMED_OPERATION_INVOCATION} : {PREFIX_PAREN}",
        r"{NUM_COMPARAND} : {FACTOR}",
        r"{NUM_COMPARAND} : {SUM}",
        r"{NUM_COMPARAND} : {PRODUCT}",
        r"{NUM_EXPR} : {PRODUCT}",
        r"{NUM_EXPR} : {SUM}",
        r"{RHSS} : {RHS}",
        r"{SETTABLE} : {DOTTING}",
        r"{TERM} : {FACTOR}",
        r"{TERM} : {PRODUCT}",
        r"{TYPE_ARG} : {DOTTING}",
        r"{TYPE_ARG} : {var}",
    ]:
        [child] = children
        return tc_expr(child, env0, expr_value_will_be_discarded)

    # ------------------------------------------------------
    # literals

    elif p == r"{LITERAL} : {BOOL_LITERAL}":
        return (T_Boolean, env0)

    elif p == r'{LITERAL} : *undefined*':
        return (T_Undefined, env0)

    elif p == r'{LITERAL} : *null*':
        return (T_Null, env0)

    elif p == r"{LITERAL} : {atat_word}":
        return (T_Symbol, env0)

    elif p == r"{NUM_LITERAL} : +&infin;":
        return (T_MathPosInfinity_, env0)

    elif p == r"{NUM_LITERAL} : -&infin;":
        return (T_MathNegInfinity_, env0)

    elif p == r"{LITERAL} : {TYPE_NAME}":
        [type_name] = children
        return (T_LangTypeName_, env0)

    elif p == r"{LITERAL} : {tilded_word}":
        [tilded_word] = children
        chars = tilded_word.source_text()[1:-1]
        if chars == 'empty':
            return (T_empty_, env0)
        elif chars == 'failure':
            return (T_match_failure_, env0)

        elif chars == 'lexical':
            # T_this_mode or T_this_binding_status_, depending on context
            # super-kludge:
            text = spec.text[expr.start_posn-30:expr.start_posn]
            if 'ThisBindingStatus' in text:
                return (T_this_binding_status_, env0)
            elif 'ThisMode' in text or '_thisMode_' in text:
                return (T_this_mode, env0)
            assert 0, text

        elif chars == 'async':
            # T_IteratorKind_ or T_FunctionKind2_
            text = spec.text[expr.start_posn-32:expr.start_posn]
            if (
                '~non-constructor~' in text
                or
                '_functionPrototype_,' in text
                or
                '_kind_ is' in text
                or
                'DynamicFunction(_C_, NewTarget,' in text
            ):
                return (T_FunctionKind2_, env0)
            elif (
                'State]]' in text
                or
                'GetGeneratorKind()' in text
                or
                '_generatorKind_' in text
                or
                '_iteratorKind_' in text
                or
                '_iteratorHint_' in text
                or
                '~sync~' in text
                or
                '_hint_' in text
                or
                '_labelSet_,' in text
            ):
                return (T_IteratorKind_, env0)

            assert 0, text

        elif chars == 'string':
            # T_PropertyKeyKind_ or T_PreferredTypeHint_
            text = spec.text[expr.start_posn-32:expr.start_posn+32]
            if (
                'GetOwnPropertyKeys' in text
                or
                '_type_' in text
            ):
                return (T_PropertyKeyKind_, env0)
            elif (
                '_hint_' in text
                or
                'ToPrimitive' in text
                or
                '_tryFirst_' in text
            ):
                return (T_PreferredTypeHint_, env0)
            else:
                assert 0, text

        elif chars in ['global', 'strict']:
            return (T_this_mode, env0)
        elif chars in ['initialized', 'uninitialized']:
            return (T_this_binding_status_, env0)
        elif chars in ['enumerate', 'iterate', 'async-iterate']:
            return (T_IterationKind_, env0)
        elif chars in ['assignment', 'varBinding', 'lexicalBinding']:
            return (T_LhsKind_, env0)
        elif chars in ['non-generator', 'async', 'sync']:
            return (T_IteratorKind_, env0)
        elif chars in ['simple', 'invalid']:
            return (T_AssignmentTargetType_, env0)
        elif chars in ['SeqCst', 'Unordered', 'Init']:
            return (T_SharedMemory_ordering_, env0)
        elif chars in ['normal', 'non-constructor', 'classConstructor', 'generator', 'async', 'asyncGenerator']:
            return (T_FunctionKind2_, env0)
        elif chars in ['base', 'derived']:
            return (T_constructor_kind_, env0)
        elif chars in [
            'BigInt64',
            'BigUint64',
            'Float32',
            'Float64',
            'Int16',
            'Int32',
            'Int8',
            'Uint16',
            'Uint32',
            'Uint8',
            'Uint8C',
        ]:
            return (T_TypedArray_element_type_, env0)
        elif chars in ['BigInt', 'Number']:
            return (T_numeric_primitive_type_, env0)
        elif chars in ['suspendedStart', 'suspendedYield', 'executing', 'completed', 'awaiting-return']:
            return (T_generator_state_, env0)
        elif chars in ['start', 'end', 'start+end']:
            return (T_TrimString_where_, env0)
        elif chars in ['key', 'value', 'key+value']:
            return (T_iteration_result_kind_, env0)
        elif chars in ['Fulfill', 'Reject']:
            return (T_settlement_type_, env0)
        elif chars in ['pending', 'fulfilled', 'rejected']:
            return (T_promise_state_, env0)
        elif chars in ['unlinked', 'linking', 'linked', 'evaluating', 'evaluating-async', 'evaluated']:
            return (T_module_record_status_, env0)
        elif chars in ['frozen', 'sealed']:
            return (T_integrity_level_, env0)
        elif chars in ['lexical-this', 'non-lexical-this']:
            return (T_this_mode2_, env0)
        elif chars in ['symbol']:
            return (T_PropertyKeyKind_, env0)
        elif chars in ['ConstructorMethod', 'NonConstructorMethod']:
            return (T_ClassElementKind_, env0)
        elif chars in ['number']:
            return (T_PreferredTypeHint_, env0)
        elif chars == 'unresolvable':
            return (T_Unresolvable_, env0)
        elif chars in ['field', 'method', 'accessor']:
            return (T_PrivateElementKind_, env0)
        elif chars in ['forward', 'backward']:
            return (T_RegExpDirection_, env0)
        elif chars == 'all':
            return (T_TildeAll_, env0)
        elif chars == 'all-but-default':
            return (T_TildeAllButDefault_, env0)
        elif chars == 'ambiguous':
            return (T_TildeAmbiguous_, env0)
        elif chars == 'namespace':
            return (T_TildeNamespace_, env0)
        elif chars == 'namespace-object':
            return (T_TildeNamespaceObject_, env0)
        elif chars == 'unused':
            return (T_TildeUnused_, env0)
        else:
            assert 0, chars

    # --------------------------------------------------------
    # introduce metavariables:

    elif p == r'{EXPR} : {EX}, where {var} is {EX}':
        [exa, var, exb] = children
        (exb_type, env1) = tc_expr(exb, env0); assert env1 is env0
        env2 = env1.plus_new_entry(var, exb_type)
        (exa_type, env3) = tc_expr(exa, env2)
        return (exa_type, env3)

    elif p in [
        r'{EXPR} : {EX}, where {var} is {EX} and {var} is {EX}',
        r'{EXPR} : {EX}, where {var} is {EX}, and {var} is {EX}',
    ]:
        [ex3, var2, ex2, var1, ex1] = children

        (ex1_type, ex1_env) = tc_expr(ex1, env0); assert ex1_env is env0
        env1 = ex1_env.plus_new_entry(var1, ex1_type)

        (ex2_type, ex2_env) = tc_expr(ex2, env1); assert ex2_env is env1
        env2 = ex2_env.plus_new_entry(var2, ex2_type)

        (ex3_type, ex3_env) = tc_expr(ex3, env2); assert ex3_env is env2
        return (ex3_type, ex3_env)

    # --------------------------------------------------------
    # invocation of named operation:

    elif p == r"{NAMED_OPERATION_INVOCATION} : {h_emu_meta_start}{NAMED_OPERATION_INVOCATION}{h_emu_meta_end}":
        [_, noi, _] = children
        return tc_expr(noi, env0)

    elif p == r"{NAMED_OPERATION_INVOCATION} : {PREFIX_PAREN} (see {h_emu_xref})":
        [pp, _] = children
        return tc_expr(pp, env0)

    elif p in [
        r"{NAMED_OPERATION_INVOCATION} : the {cap_word} of {LOCAL_REF}",
        r"{NAMED_OPERATION_INVOCATION} : the {cap_word} of {LOCAL_REF} (see {h_emu_xref})",
        r"{NAMED_OPERATION_INVOCATION} : the {cap_word} of {LOCAL_REF} as defined in {h_emu_xref}",
        r"{NAMED_OPERATION_INVOCATION} : {cap_word} of {LOCAL_REF}",
        r"{NAMED_OPERATION_INVOCATION} : the result of performing {cap_word} on {EX}",
    ]:
        [callee, local_ref] = children[0:2]
        callee_op_name = callee.source_text()
        if callee_op_name in ['UTF16EncodeCodePoint', 'UTF16SurrogatePairToCodePoint']:
            # An abstract operation that uses SDO-style invocation.
            return tc_ao_invocation(callee_op_name, [local_ref], expr, env0)
        else:
            return tc_sdo_invocation(callee_op_name, local_ref, [], expr, env0)

    elif p in [
        r"{NAMED_OPERATION_INVOCATION} : the {cap_word} of {LOCAL_REF} {WITH_ARGS}",
        r"{NAMED_OPERATION_INVOCATION} : {cap_word} of {LOCAL_REF} {WITH_ARGS}",
    ]:
        [callee, local_ref, with_args] = children
        callee_op_name = callee.source_text()
        if with_args.prod.rhs_s in [
            'with argument {EX}',
            'with arguments {EX} and {EX}',
            'with arguments {var}, {var}, and {var}',
        ]:
            args = with_args.children
        else:
            assert 0, with_args.prod.rhs_s
        return tc_sdo_invocation(callee_op_name, local_ref, args, expr, env0)

    elif p in [
        r"{NAMED_OPERATION_INVOCATION} : {LOCAL_REF} Contains {var}",
        r"{NAMED_OPERATION_INVOCATION} : {LOCAL_REF} Contains {G_SYM}",
    ]:
        [lhs, rhs] = children
        return tc_sdo_invocation('Contains', lhs, [rhs], expr, env0)


    # ------

    elif p in [
        r'{PREFIX_PAREN} : {OPN_BEFORE_PAREN}({EXLIST_OPT})',
    ]:
        [opn_before_paren, arglist] = children[0:2]
        args = exes_in_exlist_opt(arglist)

        if opn_before_paren.prod.rhs_s == '{h_emu_meta_start}{OPN_BEFORE_PAREN}{h_emu_meta_end}':
            (_, opn_before_paren, _) = opn_before_paren.children

        if opn_before_paren.prod.rhs_s in [
            r'{DOTTING}',
            r'{var}',
        ]:
            [thing] = opn_before_paren.children
            (t, env0) = tc_expr(thing, env0)
            assert isinstance(t, ProcType)
            params = with_fake_param_names(t.param_types)
            return_type = t.return_type

        elif opn_before_paren.prod.rhs_s == r'{var}.{cap_word}':
            [var, cap_word] = opn_before_paren.children
            callee_op_name = cap_word.source_text()

            callee_op = spec.alg_info_['op'][callee_op_name]
            assert callee_op.species in [
                'op: discriminated by type: env rec',
                'op: discriminated by type: module rec',
            ]

            # XXX If PR #955 is accepted, that will change things around here.

            # When there's a type hierarchy (under Environment Record or Module Record),
            # and sub-types augment the set of types defined at the root,
            # then the use of one of those added methods
            # implies a tighter constraint on the type of the LHS.

            assert len(callee_op.headers) > 0
            forp_types = [
                header.tah.for_param_type
                for header in callee_op.headers
            ]
            if callee_op_name in ['Link', 'Evaluate']:
                # These are abstract methods of all Module Records,
                # but the spec only has definitions for Cyclic Module Records.
                forp_types.append(T_other_Module_Record)
            elif callee_op_name in ['GetExportedNames', 'ResolveExport']:
                # These are abstract methods of all Module Records,
                # but the spec only has definitions for Source Text Module Records.
                forp_types.append(T_other_Module_Record)
                forp_types.append(T_other_Cyclic_Module_Record)
            elif callee_op_name in ['InitializeEnvironment', 'ExecuteModule']:
                # These are abstract methods of all Cyclic Module Records,
                # but the spec only has definitions for Source Text Module Records.
                forp_types.append(T_other_Cyclic_Module_Record)

            union_of_forp_types = union_of_types(forp_types)

            env0 = env0.ensure_expr_is_of_type(var, union_of_forp_types)

            params = callee_op.parameters_with_types
            return_type = callee_op.return_type

        elif opn_before_paren.prod.rhs_s == '{SIMPLE_OPERATION_NAME}':
            callee_op_name = opn_before_paren.source_text()

            # NormalCompletion and ThrowCompletion are regular abstract operations now,
            # so you might expect that we'd use their deduced return types.
            # However, that would lose information, so we don't.

            if callee_op_name == 'NormalCompletion':
                assert len(args) == 1
                [arg] = args
                (arg_type, arg_env) = tc_expr(arg, env0); assert arg_env is env0
                assert arg_type == T_TBD or arg_type.is_a_subtype_of_or_equal_to(T_Normal)
                return_type = arg_type
                return (return_type, env0)
                # don't call tc_args etc

            elif callee_op_name == 'ThrowCompletion':
                assert len(args) == 1
                [arg] = args
                (arg_type, arg_env) = tc_expr(arg, env0); assert arg_env is env0
                if arg_type == T_TBD: arg_type = T_Normal
                assert arg_type.is_a_subtype_of_or_equal_to(T_Normal)
                return_type = ThrowType(arg_type)
                return (return_type, env0)

            elif callee_op_name == 'Completion':
                assert len(args) == 1
                [arg] = args
                (arg_type, env1) = tc_expr(arg, env0)
                return_type = arg_type # bleah
                return (return_type, env1)

            elif callee_op_name == 'Await':
                assert len(args) == 1
                [arg] = args
                env0.assert_expr_is_of_type(arg, T_Tangible_|T_empty_)
                return (T_Tangible_|T_empty_|T_return_|T_throw_, env0)

            elif callee_op_name == 'abs':
                assert len(args) == 1
                [arg] = args
                (arg_type, arg_env) = tc_expr(arg, env0); assert arg_env is env0
                if arg_type.is_a_subtype_of_or_equal_to(T_MathInteger_):
                    return (T_MathInteger_, env0)
                elif arg_type.is_a_subtype_of_or_equal_to(T_MathReal_):
                    return (T_MathReal_, env0)
                else:
                    add_pass_error(
                        arg,
                        f"expected a MathReal, got {arg_type}"
                    )
                    return (T_MathReal_, env0)

            elif callee_op_name == 'floor':
                assert len(args) == 1
                [arg] = args
                env1 = env0.ensure_expr_is_of_type(arg, T_MathReal_)
                return (T_MathInteger_, env1)

            elif callee_op_name == '\u211d': # DOUBLE-STRUCK CAPITAL R (fancy_r)
                assert len(args) == 1
                [arg] = args
                (arg_type, arg_env) = tc_expr(arg, env0)
                if arg_type.is_a_subtype_of_or_equal_to(T_BigInt | T_IntegralNumber_):
                    return (T_MathInteger_, arg_env)
                elif arg_type.is_a_subtype_of_or_equal_to(T_FiniteNumber_):
                    return (T_MathReal_, env0)
                elif arg_type.is_a_subtype_of_or_equal_to(T_FiniteNumber_ | T_InfiniteNumber_):
                    # This isn't correct: fancy_r is "mathematical value",
                    # which is not defined on non-finite values.
                    # However, it makes lots of invalid complaints go away.
                    return (T_ExtendedMathReal_, env0)
                else:
                    add_pass_error(
                        arg,
                        f"expected a BigInt or a non-NaN Number, got {arg_type}"
                    )
                    return (T_ExtendedMathReal_, env0)

            elif callee_op_name == '\u2124': # DOUBLE-STRUCK CAPITAL Z (fancy_z)
                assert len(args) == 1
                [arg] = args
                env0.assert_expr_is_of_type(arg, T_MathInteger_)
                return (T_BigInt, env0)

            elif callee_op_name == '\U0001d53d': # MATHEMATICAL DOUBLE-STRUCK CAPITAL F (fancy_f)
                assert len(args) == 1
                [arg] = args
                (t, env1) = tc_expr(arg, env0)
                if t.is_a_subtype_of_or_equal_to(T_MathInteger_):
                    result_type = T_IntegralNumber_
                elif t.is_a_subtype_of_or_equal_to(T_MathInteger_ | T_MathPosInfinity_ | T_MathNegInfinity_):
                    result_type = T_IntegralNumber_ | T_InfiniteNumber_
                elif t.is_a_subtype_of_or_equal_to(T_MathReal_):
                    result_type = T_Number
                elif t == T_TBD:
                    result_type = T_IntegralNumber_ # hm
                else:
                    add_pass_error(arg,
                        f"ERROR: arg is of type {t} but fancy_f requires MathReal"
                    )
                    result_type = T_Number
                return (result_type, env1)

            elif callee_op_name in ['min', 'max']:
                assert len(args) == 2
                env1 = env0
                argtypes = []
                for arg in args:
                    (t, env1) = tc_expr(arg, env1)
                    if not t.is_a_subtype_of_or_equal_to(T_ExtendedMathReal_):
                        add_pass_error(arg,
                            f"arg is of type {t} but param requires ExtendedMathReal"
                        )
                        if t == T_MathInteger_ | T_empty_:
                            # InnerModuleEvaluation
                            t = T_MathInteger_
                    argtypes.append(t)

                if callee_op_name == 'min':
                    # We allow an arg to be +infinity, but that won't be the result.
                    # (As long as both args aren't +infinity.)
                    add_type = T_MathPosInfinity_
                else:
                    add_type = T_MathNegInfinity_

                for math_type in [T_MathInteger_, T_MathReal_, T_ExtendedMathReal_]:
                    if all(
                        t.is_a_subtype_of_or_equal_to(math_type | add_type)
                        for t in argtypes
                    ):
                        return (math_type, env1)
                assert 0
                return (T_ExtendedMathReal_, env1)

            elif callee_op_name in [
                # 30232 Day Number and Time within Day
                'Day',
                'TimeWithinDay',

                # 30264 Month Number
                'MonthFromTime',

                # 30286 Date Number
                'DateFromTime',

                # 30305 Week Day
                'WeekDay',

                # 30376 Hours, Minutes, Second, and Milliseconds
                'HourFromTime',
                'MinFromTime',
                'SecFromTime',
                'msFromTime',

                # 'DaylightSavingTA',
            ]:
                assert len(args) == 1
                [arg] = args
                env1 = env0.ensure_expr_is_of_type(arg, T_FiniteNumber_)
                return (T_FiniteNumber_, env1)

            # 30424 Year Number
            elif callee_op_name == 'YearFromTime':
                assert len(args) == 1
                [arg] = args
                env1 = env0.ensure_expr_is_of_type(arg, T_Number)
                return (T_IntegralNumber_, env1)


            # ---------------

            else:
                callee_op = spec.alg_info_['op'][callee_op_name]
                if callee_op.species == 'op: discriminated by syntax: steps':
                    add_pass_error(
                        expr,
                        "Unusual to invoke a SDO via prefix-paren notation: " + expr.source_text()
                    )
                    assert len(args) == 1
                    return tc_sdo_invocation(callee_op_name, args[0], [], expr, env0)
                else:
                    assert callee_op.species.startswith('op: singular'), callee_op.species
                params = callee_op.parameters_with_types
                return_type = callee_op.return_type
                # fall through to tc_args etc

                # if callee_op_name == 'ResolveBinding': pdb.set_trace()

        else:
            assert 0, opn_before_paren.prod.rhs_s

        # context = 'in call to `%s`' % opn_before_paren.source_text()
        env2 = tc_args(params, args, env0, expr)
        return (return_type, env2)

    # --------------------------------------------------------

    elif p == r"{SETTABLE} : the {DSBN} field of {EXPR}":
        [dsbn, ex] = children
        dsbn_name = dsbn.source_text()[2:-2]
        if dsbn_name == 'EventList':
            env0.assert_expr_is_of_type(ex, T_Agent_Events_Record)
            return (ListType(T_event_), env0)
        elif dsbn_name == 'CandidateExecution':
            env0.assert_expr_is_of_type(ex, T_Agent_Record)
            return (T_candidate_execution, env0)
        elif dsbn_name == 'LittleEndian':
            env0.assert_expr_is_of_type(ex, T_Agent_Record)
            return (T_Boolean, env0)
        else:
            assert 0, expr

    elif p in [
        r'{DOTTING} : {var}.{DSBN}',
        r"{DOTTING} : {DOTTING}.{DSBN}",
    ]:
        [lhs_var, dsbn] = children
        lhs_text = lhs_var.source_text()
        dsbn_name = dsbn.source_text()[2:-2]
        (lhs_t, env1) = tc_expr(lhs_var, env0)

        # assert dsbn_name != 'Type'
        # because anything involving [[Type]] has been intercepted at a higher level
        # Nope, _reaction_.[[Type]]

        # ----------------------------------

        # Handle "Completion Records" specially.
        while True: # ONCE
            if dsbn_name not in ['Type', 'Target', 'Value']:
                # We can't be dealing with a Completion Record
                break
            if lhs_t in [
                T_ImportMeta_record_,
                T_MapData_record_,
                T_PromiseReaction_Record,
                T_Property_Descriptor,
                T_boolean_value_record_,
                T_boolean_value_record_ | T_Boolean,
                T_integer_value_record_,
            ]:
                # We know we're not dealing with a Completion Record
                break

            assert lhs_text not in [
                '_D_',
                '_Desc_',
                '_alreadyResolved_',
                '_current_',
                '_desc_',
                '_like_',
                '_newLenDesc_',
                '_oldLenDesc_',
                '_reaction_',
                '_remainingElementsCount_',
            ]

            result_memtypes = set()
            for memtype in lhs_t.set_of_types():
                if dsbn_name == 'Value':
                    # Lots of things have a '[[Value]]' field.
                    if memtype.is_a_subtype_of_or_equal_to(T_Abrupt):
                        result_memtype = T_Tangible_ | T_empty_
                    elif memtype == T_Normal:
                        result_memtype = T_Tangible_ | T_empty_
                    elif memtype.is_a_subtype_of_or_equal_to(T_Tangible_ | T_empty_):
                        result_memtype = memtype

                    elif memtype.is_a_subtype_of_or_equal_to(T_Reference_Record):
                        # Completion Record's [[Value]] can be a Reference Record, despite the definition of CR?
                        result_memtype = memtype
                    elif memtype == T_Realm_Record:
                        # GetFunctionRealm can supposedly return a Completion Record whose [[Value]] is a Realm Record, despite the definition of CR
                        result_memtype = memtype
                    elif memtype in [T_ClassFieldDefinition_Record, T_ClassStaticBlockDefinition_Record]:
                        # ClassDefinitionEvaluation: `Set _element_ to _element_.[[Value]].`
                        result_memtype = memtype
                    elif memtype in [T_TildeUnused_, ListType(T_code_unit_), T_Top_]:
                        # hm.
                        result_memtype = memtype

                    elif memtype.is_a_subtype_of_or_equal_to(T_Private_Name):
                        result_memtype = T_function_object_
                    elif memtype == T_Record:
                        # All we know is that it's a Record with a [[Value]] field.
                        result_memtype = T_TBD
                    elif memtype == T_PrivateElement:
                        result_memtype = T_Tangible_
                    else:
                        assert 0, memtype

                elif dsbn_name == 'Target':
                    if memtype in [T_continue_, T_break_, T_Abrupt]:
                        result_memtype = T_String | T_empty_
                    else:
                        assert 0, memtype

                elif dsbn_name == 'Type':
                    assert 0

                else:
                    assert 0

                result_memtypes.add(result_memtype)

            result_type = union_of_types(result_memtypes)
            return (result_type, env1)

        # Finished with "Completion Records"
        # ----------------------------------

        # In some cases, we first need to change the type of lhs_var...

        if lhs_t == T_0:
            if lhs_text == '_starResolution_':
                # ResolveExport _starResolution_
                # The first time through the For loop,
                # _starResolution has type Null,
                # so after "If _starResolution_ is *null*,",
                # in the Else branch it has type T_0.
                # Properly, that should make us not do STA on the Else branch,
                # then we would re-STA the loop-body
                # with a wider type for _starResolution_.
                # But I'm hoping to avoid the need to re-STA loop-bodies.
                lhs_t = T_ResolvedBinding_Record
            elif lhs_text == '_element_':
                lhs_t = T_PrivateElement
            else:
                assert 0, expr.source_text()
            add_pass_error(
                expr,
                "`%s` has type T_0, changing to %s" % (lhs_text, lhs_t)
            )
            env2 = env1

        elif lhs_t == T_Property_Descriptor | T_Undefined:
            # CreateGlobalFunctionBinding:
            # If _existingProp_ is *undefined* or _existingProp_.[[Configurable]] is *true*
            lhs_t = T_Property_Descriptor
            env2 = env1.with_expr_type_replaced(lhs_var, lhs_t)

        elif lhs_t in [
            T_Object | T_Boolean | T_Environment_Record | T_Number | T_String | T_Symbol | T_Undefined,
            T_Object | T_Null,
            T_Object | T_Undefined,
        ]:
            # GetValue. (Fix by replacing T_Reference_Record with ReferenceType(base_type)?)
            lhs_t = T_Object
            env2 = env1.with_expr_type_replaced(lhs_var, lhs_t)

        elif lhs_t == T_boolean_value_record_ | T_Boolean:
            lhs_t = T_boolean_value_record_
            env2 = env1.with_expr_type_replaced(lhs_var, lhs_t)

        elif lhs_t == T_Realm_Record | T_Undefined:
            lhs_t = T_Realm_Record
            env2 = env1.with_expr_type_replaced(lhs_var, lhs_t)

        elif lhs_t == T_Cyclic_Module_Record | T_empty_:
            assert lhs_text in ['_m_.[[CycleRoot]]', '_module_', '_requiredModule_']
            lhs_t = T_Cyclic_Module_Record
            env2 = env1.with_expr_type_replaced(lhs_var, lhs_t)

        elif lhs_t in [
            T_TBD,
            T_Top_,
            T_Tangible_,
            T_Normal,
            T_empty_,
            T_Tangible_ | T_empty_,
            T_Tangible_ | T_empty_ | T_Abrupt,
        ]:
            # Have to peek at the dsbn to infer the type of the lhs_var.

            candidate_type_names = []

            for (record_type_name, fields) in sorted(fields_for_record_type_named_.items()):
                if dsbn_name in fields:
                    candidate_type_names.append(record_type_name)

            if dsbn_name in type_of_internal_thing_:
                candidate_type_names.append('Object')
                # But we could sometimes be more specific about the kind of Object:
                # 'PromiseState'    : Promise Instance object
                # 'TypedArrayName'  : Integer Indexed object
                # 'GeneratorState'  : Generator Instance
                # 'OriginalSource'  : RegExp Instance
                # 'GeneratorContext': Generator Instance

            if dsbn_name == 'Realm':
                assert candidate_type_names == ['Cyclic Module Record', 'Job_record_', 'Module Record', 'Script Record', 'Source Text Module Record', 'other Module Record', 'Object']
                if lhs_text == '_scriptRecord_':
                    lhs_t = T_Script_Record
                else:
                    assert 0
            elif dsbn_name == 'Done':
                assert candidate_type_names == ['Iterator Record', 'Object']
                assert lhs_text == '_iteratorRecord_'
                lhs_t = T_Iterator_Record
            else:
                assert len(candidate_type_names) == 1, (dsbn_name, candidate_type_names)
                [type_name] = candidate_type_names
                lhs_t = NamedType(type_name)

            env2 = env1.with_expr_type_replaced(lhs_var, lhs_t)

        else:
            env2 = env1

        # --------------------------------------------

        if lhs_t.is_a_subtype_of_or_equal_to(T_Object):
            # _foo_.[[Bar]] references an object's internal method or internal slot.

            it_type = type_of_internal_thing_[dsbn_name]

            # XXX We should require that lhs_t is allowed to have this internal thing.

            # But for some subtypes of Object, we can give a narrower type for the slot
            if lhs_t == T_SharedArrayBuffer_object_ and dsbn_name == 'ArrayBufferData':
                narrower_type = T_Shared_Data_Block
                assert narrower_type.is_a_subtype_of_or_equal_to(it_type)
                assert narrower_type != it_type
                it_type = narrower_type
            return (it_type, env2)

        elif lhs_t == T_Symbol:
            assert dsbn_name == 'Description'
            return (T_String | T_Undefined, env2)

        elif lhs_t == T_Private_Name:
            assert dsbn_name == 'Description'
            return (T_String, env2)

        elif lhs_t.is_a_subtype_of_or_equal_to(T_Record):
            # _foo_.[[Bar]] references a record's field
            if isinstance(lhs_t, NamedType):
                if lhs_t.name == 'Record':
                    add_pass_error(
                        expr,
                        "type of `%s` is only 'Record', so don't know about a `%s` field"
                        % (lhs_text, dsbn_name)
                    )
                    for record_type_name in [
                        'Property Descriptor', # for the almost-Property Descriptor in CompletePropertyDescriptor
                        'Iterator Record',
                        'templateMap_entry_',
                        'methodDef_record_',
                        'CodePointAt_record_',
                        'Job_record_',
                        'FinalizationRegistryCellRecord_',
                    ]:
                        pd_fields = fields_for_record_type_named_[record_type_name]
                        if dsbn_name in pd_fields:
                            field_type = pd_fields[dsbn_name]
                            break
                    else:
                        assert 0, dsbn_name
                        # Need to add something to fields_for_record_type_named_?
                elif lhs_t.name == 'Intrinsics Record':
                    field_type = {
                        '%Array%'               : T_constructor_object_,
                        '%Function.prototype%'  : T_Object,
                        '%Object.prototype%'    : T_Object,
                        '%ThrowTypeError%'      : T_function_object_,
                    }[dsbn_name]
                else:
                    assert lhs_t.name in fields_for_record_type_named_, lhs_t.name
                    fields_info = fields_for_record_type_named_[lhs_t.name]
                    if dsbn_name in fields_info:
                        field_type = fields_info[dsbn_name]
                    else:
                        add_pass_error(
                            expr,
                            f"`{lhs_text}` has type {lhs_t}, which doesn't have a `{dsbn_name}` field"
                        )
                        # Probably you need to add something to
                        # fields_for_record_type_named_

                        field_type = T_TBD

                return (field_type, env2)

            elif isinstance(lhs_t, UnionType):
                types_for_field = set()
                for mt in lhs_t.member_types:
                    fields_info = fields_for_record_type_named_[mt.name]
                    assert dsbn_name in fields_info
                    field_type = fields_info[dsbn_name]
                    types_for_field.add(field_type)
                assert len(types_for_field) == 1
                field_type = types_for_field.pop()
                return (field_type, env2)

            else:
                assert 0, (expr.source_text(), lhs_t)

        else:
            # assert 0, (expr.source_text(), str(lhs_t))
            add_pass_error(
                lhs_var,
                f"How does something of type {lhs_t} support a dot-operator?"
            )
            return (T_TBD, env2)

    # -------------------------------------------------

    elif p == r"{EXPR} : {EX} if {CONDITION}. Otherwise, it is {EXPR}":
        [exa, cond, exb] = children
        (t_env, f_env) = tc_cond(cond, env0)
        (ta, enva) = tc_expr(exa, t_env)
        (tb, envb) = tc_expr(exb, f_env)
        return (ta | tb, env_or(enva, envb))

    # -------------------------------------------------
    # return T_BigInt

    elif p == r"{NUM_LITERAL} : {starred_int_lit}{h_sub_fancy_z}":
        [_, _] = children
        return (T_BigInt, env0)

    elif p == r"{EXPR} : the BigInt value that represents {EX}":
        [ex] = children
        env0.assert_expr_is_of_type(ex, T_MathReal_|T_BigInt)
        return (T_BigInt, env0)

    elif p == r"{EXPR} : the BigInt value that corresponds to {var}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_MathInteger_)
        return (T_BigInt, env0)

    elif p == r"{EX} : the BigInt value for {EX}":
        [ex] = children
        env0.assert_expr_is_of_type(ex, T_MathInteger_)
        return (T_BigInt, env0)

    elif p == r"{EXPR} : the BigInt defined by the mathematical relation {var} = {var} - ({var} &times; {var}) where {var} is a BigInt that is negative only if {var}/{var} is negative and positive only if {var}/{var} is positive, and whose magnitude is as large as possible without exceeding the magnitude of the true mathematical quotient of {var} and {var}":
        # XXX
        return (T_BigInt, env0)

    elif p in [
        r"{EX} : the sum of {var} and {var}",
        r"{EX} : the product of {var} and {var}",
        r"{EX} : the difference {var} minus {var}",
    ]:
        [x, y] = children
        env0.assert_expr_is_of_type(x, T_BigInt)
        env0.assert_expr_is_of_type(y, T_BigInt)
        return (T_BigInt, env0)

    # -------------------------------------------------
    # return T_Number

    elif p == r"{NUM_LITERAL} : {starred_infinite_lit}{h_sub_fancy_f}":
        return (T_InfiniteNumber_, env0)

    elif p in [
        r"{NUM_LITERAL} : {starred_nan_lit}",
        r'{NUM_LITERAL} : the *NaN* Number value',
    ]:
        return (T_NaN_Number_, env0)

    elif p in [
        r"{NUM_LITERAL} : *0.5*{h_sub_fancy_f}",
        r"{NUM_LITERAL} : *-0.5*{h_sub_fancy_f}",
    ]:
        return (T_NonIntegralFiniteNumber_, env0)

    elif p == r"{NUM_LITERAL} : {starred_int_lit}{h_sub_fancy_f}":
        [_, _] = children
        return (T_IntegralNumber_, env0)

    elif p == r'{EXPR} : the Number value that corresponds to {var}':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_IEEE_binary32_ | T_IEEE_binary64_ | T_MathInteger_)
        return (T_Number, env1)

    elif p == r"{EX} : the Number value for {EX}":
        [ex] = children
        (ex_type, env1) = tc_expr(ex, env0)
        # env1 = env0.ensure_expr_is_of_type(ex, T_MathReal_)
        if ex_type.is_a_subtype_of_or_equal_to(T_MathInteger_):
            return (T_IntegralNumber_, env1)
        elif ex_type.is_a_subtype_of_or_equal_to(T_MathInteger_ | T_MathPosInfinity_ | T_MathNegInfinity_):
            return (T_IntegralNumber_ | T_InfiniteNumber_, env1)
        elif ex_type.is_a_subtype_of_or_equal_to(T_ExtendedMathReal_):
            return (T_Number, env1)
        else:
            add_pass_error(
                ex,
                f"expected MathReal, got {ex_type}"
            )
            return (T_Number, env1)

    elif p in [
        r"{EXPR} : the Element Size value specified in {h_emu_xref} for Element Type {var}",
    ]:
        [emu_xref, var] = children
        assert var.source_text() in ['_type_', '_srcType_', '_elementType_']
        env1 = env0.ensure_expr_is_of_type(var, T_TypedArray_element_type_)
        return (T_MathInteger_, env1)

    elif p in [
        r"{EXPR} : the Element Size value specified in {h_emu_xref} for {EX}",
    ]:
        [emu_xref, ex] = children
        env1 = env0.ensure_expr_is_of_type(ex, T_String)
        return (T_MathInteger_, env1)

    elif p == r"{EXPR} : (({var} `*` msPerHour `+` {var} `*` msPerMinute) `+` {var} `*` msPerSecond) `+` {var}, performing the arithmetic according to IEEE 754-2019 rules (that is, as if using the ECMAScript operators `*` and `+`)":
        for var in children:
            env0.assert_expr_is_of_type(var, T_Number)
        return (T_Number, env0)

    elif p in [
        r"{EXPR} : the result of negating {var}; that is, compute a Number with the same magnitude but opposite sign",
    ]:
        [var] = children
        env0.assert_expr_is_of_type(var, T_Number)
        return (T_Number, env0)

    elif p == r"{EXPR} : the result of applying bitwise complement to {var}. The mathematical value of the result is exactly representable as a 32-bit two's complement bit string":
        [var] = children
        env0.assert_expr_is_of_type(var, T_IntegralNumber_)
        return (T_IntegralNumber_, env0)

    elif p in [
        r"{EX} : the result of left shifting {var} by {var} bits. The mathematical value of the result is exactly representable as a 32-bit two's complement bit string",
        r"{EXPR} : the result of performing a sign-extending right shift of {var} by {var} bits. The most significant bit is propagated. The mathematical value of the result is exactly representable as a 32-bit two's complement bit string",
        r"{EXPR} : the result of performing a zero-filling right shift of {var} by {var} bits. Vacated bits are filled with zero. The mathematical value of the result is exactly representable as a 32-bit unsigned bit string",
    ]:
        [avar, bvar] = children
        env1 = env0.ensure_expr_is_of_type(avar, T_IntegralNumber_)
        env1.assert_expr_is_of_type(bvar, T_MathInteger_)
        return (T_IntegralNumber_, env1)

    elif p in [
        r"{EXPR} : the smallest (closest to -&infin;) integral Number value that is not less than {var}",
        r"{EXPR} : the greatest (closest to +&infin;) integral Number value that is not greater than {var}",
        r"{EXPR} : the integral Number closest to {var}, preferring the Number closer to +&infin; in the case of a tie",
    ]:
        [var] = children
        env0.assert_expr_is_of_type(var, T_Number)
        return (T_Number, env0)

    elif p == r"{EXPR} : the integral Number nearest {var} in the direction of *+0*{h_sub_fancy_f}":
        [var, _] = children
        env0.assert_expr_is_of_type(var, T_Number)
        return (T_Number, env0)

    # --------------------------------------------------------
    # return T_MathInteger_

    elif p in [
        r"{EX} : the number of code points in {PROD_REF}, excluding all occurrences of {nonterminal}",
        r"{EX} : the number of code points in {PROD_REF}, excluding all occurrences of {nonterminal}",
    ]:
        [prod_ref, nont] = children
        return (T_MathNonNegativeInteger_, env0)

    elif p == r"{EX} : {var} rounded towards 0 to the next integer value":
        [var] = children
        env0.assert_expr_is_of_type(var, T_MathReal_)
        return (T_MathInteger_, env0)

    elif p == r"{NUM_EXPR} : {EX} raised to the power {EX}":
        [a, b] = children
        env0.assert_expr_is_of_type(a, T_MathInteger_)
        env0.assert_expr_is_of_type(b, T_MathInteger_)
        return (T_MathInteger_, env0) # unless exponent is negative

    elif p == r"{EX} : the integer represented by the 32-bit two's complement bit string {var}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_MathInteger_) # bit string
        return (T_MathInteger_, env0)

    elif p == r"{EX} : {EX}, rounding down to the nearest integer, including for negative numbers":
        [ex] = children
        env0.assert_expr_is_of_type(ex, T_MathReal_)
        return (T_MathInteger_, env0)

    # --------------------------------------------------------
    # return T_MathReal_

    elif p in [
        r"{NUM_LITERAL} : 8.64",
        r"{NUM_LITERAL} : 0.5",
    ]:
        return (T_MathReal_, env0)

    elif p in [
        r'{EXPR} : the negative of {EX}',
    ]:
        [ex] = children
        (ex_t, env1) = tc_expr(ex, env0); assert env1 is env0
        assert ex_t == T_TBD or ex_t == T_MathInteger_
        return (ex_t, env0)

    elif p == r"{PRODUCT} : the negation of {EX}":
        [ex] = children
        env0.assert_expr_is_of_type(ex, T_MathReal_)
        return (T_MathReal_, env0)

    elif p == r"{PRODUCT} : the quotient {FACTOR} / {FACTOR}":
        [vara, varb] = children
        env1 = env0.ensure_expr_is_of_type(vara, T_MathReal_)
        env2 = env1.ensure_expr_is_of_type(varb, T_MathReal_)
        return (T_MathReal_, env2)

    elif p in [
        "{NUM_EXPR} : &pi; / 2",
        "{NUM_EXPR} : &pi; / 4",
        "{NUM_EXPR} : &pi;",
        "{NUM_EXPR} : 3&pi; / 4",
        "{NUM_EXPR} : -&pi; / 2",
        "{NUM_EXPR} : -&pi; / 4",
        "{NUM_EXPR} : -&pi;",
        "{NUM_EXPR} : -3&pi; / 4",
    ]:
        [] = children
        return (T_MathReal_, env0)

    elif p == r"{EXPR} : the result of the {MATH_FUNC} of {EX}":
        [math_func, ex] = children
        env1 = env0.ensure_expr_is_of_type(ex, T_Number | T_MathReal_)
        return (T_MathReal_, env1)

    elif p == r"{EXPR} : the result of subtracting 1 from the exponential function of {EX}":
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_MathReal_)
        return (T_MathReal_, env1)

    elif p == r"{EXPR} : the result of raising {EX} to the {EX} power":
        [avar, bvar] = children
        env1 = env0.ensure_expr_is_of_type(avar, T_MathReal_)
        env2 = env0.ensure_expr_is_of_type(bvar, T_MathReal_)
        return (T_MathReal_, env2)

    elif p == r"{EXPR} : the square root of the sum of squares of the mathematical values of the elements of {var}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_List)
        return (T_MathReal_, env0)

    elif p == r"{EXPR} : {EX} - ({EX} &times; {var}) where {var} is an integer that is negative if and only if {var} and {var} have opposite sign, and whose magnitude is as large as possible without exceeding the magnitude of {EX} / {EX}":
        [exa, exb, _, _, _, _, _, _] = children # XXX
        env1 = env0.ensure_expr_is_of_type(exa, T_MathReal_)
        env2 = env1.ensure_expr_is_of_type(exb, T_MathReal_)
        return (T_MathReal_, env2)

    # --------------------------------------------------------
    # return T_MathInteger_: The size of some collection:

    elif p in [
        r"{NUM_COMPARAND} : the length of {var}",
        r"{EX} : the length of {var}",
    ]:
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_String)
        return (T_MathNonNegativeInteger_, env1)

    elif p in [
        r"{EXPR} : the number of elements in the List {var}",
        r"{EX} : the number of elements in {var}",
    ]:
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_List)
        return (T_MathNonNegativeInteger_, env1)

    elif p == r"{EXPR} : the number of elements in {var}'s _captures_ List":
        [var] = children
        env0.assert_expr_is_of_type(var, T_State)
        return (T_MathNonNegativeInteger_, env0)

    elif p in [
        r'{EX} : the number of code points in {PROD_REF}',
    ]:
        [prod_ref] = children
        env0.assert_expr_is_of_type(prod_ref, T_Parse_Node)
        return (T_MathNonNegativeInteger_, env0)

    elif p == r"{EXPR} : the number of bytes in {var}":
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_Data_Block | T_Shared_Data_Block)
        return (T_MathNonNegativeInteger_, env1)

    elif p == r"{EXPR} : the number of non-optional parameters of the function definition in {h_emu_xref}":
        [xref] = children
        return (T_MathNonNegativeInteger_, env0)

    elif p in [
        r"{FACTOR} : {CONSTANT_NAME}",
        r"{EX} : {CONSTANT_NAME}",
    ]:
        [constant_name] = children
        constant_name_str = constant_name.source_text()
        # hack:
        result_type = {
            'HoursPerDay'      : T_MathNonNegativeInteger_,
            'MinutesPerHour'   : T_MathNonNegativeInteger_,
            'SecondsPerMinute' : T_MathNonNegativeInteger_,
            'msPerDay'         : T_FiniteNumber_,
            'msPerHour'        : T_FiniteNumber_,
            'msPerMinute'      : T_FiniteNumber_,
            'msPerSecond'      : T_FiniteNumber_,
        }[constant_name_str]
        return (result_type, env0)

    # ----
    # return T_MathInteger_: arithmetic:

    elif p in [
        r"{NUM_LITERAL} : {hex_int_lit}",
        r"{NUM_LITERAL} : {dec_int_lit}",
        r"{NUM_LITERAL} : -5",
        r"{BASE} : 10",
        r"{BASE} : 2",
    ]:
        # [] = children
        return (T_MathInteger_, env0)

    elif p in [
        r"{FACTOR} : {BASE}<sup>{EX}</sup>",
    ]:
        [base, exponent] = children
        (base_t, env1) = tc_expr(base, env0); assert env1 is env0
        if base_t == T_MathInteger_:
            env1 = env0.ensure_expr_is_of_type(exponent, T_MathReal_ | T_BigInt)
        else:
            assert 0, base_t
        return (base_t, env1) # XXX unless exponent is negative

    elif p == r"{EX} : the remainder of dividing {EX} by {EX}":
        [aex, bex] = children
        env0.assert_expr_is_of_type(aex, T_MathInteger_)
        env0.assert_expr_is_of_type(bex, T_MathInteger_)
        return (T_MathInteger_, env0)

    elif p == r"{EXPR} : the mathematical value whose sign is the sign of {var} and whose magnitude is {EX}":
        [var, ex] = children
        env0.assert_expr_is_of_type(var, T_Number)
        env0.assert_expr_is_of_type(ex, T_MathInteger_)
        return (T_MathInteger_, env0)

    elif p == r"{NUM_LITERAL} : 64 (that is, 8<sup>2</sup>)":
        [] = children
        return (T_MathInteger_, env0)

    # ----

    elif p in [
        r"{NUM_COMPARAND} : the numeric value of {var}",
        r"{EX} : the numeric value of {EX}",
    ]:
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_code_unit_ | T_code_point_)
        return (T_MathInteger_, env1)

    elif p == r"{EXPR} : the integer that is {EXPR}":
        [ex] = children
        env0.assert_expr_is_of_type(ex, T_MathInteger_)
        return (T_MathInteger_, env0)

    # ----

    elif p in [
        r'{EXPR} : the character value of character {var}',
    ]:
        [var] = children
        env0.assert_expr_is_of_type(var, T_character_)
        return (T_MathInteger_, env0)

    elif p == r"{EXPR} : the numeric value according to {h_emu_xref}":
        return (T_MathInteger_, env0)

    elif p == r'{EXPR} : the byte elements of {var} concatenated and interpreted as a bit string encoding of an unsigned little-endian binary number':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_MathInteger_))
        return (T_MathInteger_, env1)

    elif p == r"{EXPR} : the byte elements of {var} concatenated and interpreted as a bit string encoding of a binary little-endian two's complement number of bit length {PRODUCT}":
        [var, product] = children
        env1 = env0.ensure_expr_is_of_type(product, T_MathInteger_ | T_Number); assert env1 is env0
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_MathInteger_))
        return (T_MathInteger_, env1)

    elif p in [
        r"{EX} : {var}'s _endIndex_",
        r"{EX} : {var}'s _endIndex_ value",
        r"{NUM_COMPARAND} : {var}'s _endIndex_",
    ]:
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_State | T_Range)
        return (T_MathInteger_, env1)

    elif p == r"{EX} : {var}'s _startIndex_":
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_Range)
        return (T_MathInteger_, env1)

    elif p == r"{EXPR} : the index into {var} of the character that was obtained from element {EX} of {var}":
        [list_var, index_var, str_var] = children
        env0.assert_expr_is_of_type(list_var, T_List)
        env0.assert_expr_is_of_type(index_var, T_MathInteger_)
        env0.assert_expr_is_of_type(str_var, T_String) # todo: element of String
        return (T_MathInteger_, env0)

    elif p == r"{EXPR} : the number of {h_emu_grammar} Parse Nodes contained within {var}":
        [emu_grammar, root_var] = children
        env0.assert_expr_is_of_type(root_var, T_Parse_Node)
        return (T_MathNonNegativeInteger_, env0)

    elif p == r"{EXPR} : the number of {h_emu_grammar} Parse Nodes contained within {var} that either occur before {var} or contain {var}":
        [emu_grammar, root_var, x_var, x_var2] = children
        env0.assert_expr_is_of_type(root_var, T_Parse_Node)
        env0.assert_expr_is_of_type(x_var, T_Parse_Node)
        assert x_var.source_text() == x_var2.source_text()
        return (T_MathNonNegativeInteger_, env0)

    elif p == r"{EXPR} : the 8-bit value represented by the two hexadecimal digits at index {EX} and {EX}":
        [posa, posb] = children
        env0.assert_expr_is_of_type(posa, T_MathInteger_)
        env0.assert_expr_is_of_type(posb, T_MathInteger_)
        return (T_MathInteger_, env0)

    elif p == r"{EXPR} : the code point obtained by applying the UTF-8 transformation to {var}, that is, from a List of octets into a 21-bit value":
        [var] = children
        env0.assert_expr_is_of_type(var, ListType(T_MathInteger_))
        return (T_code_point_, env0)

    # ----

    elif p in [
        r"{EXPR} : the result of applying the bitwise AND operation to {var} and {var}",
        r"{EXPR} : the result of applying the bitwise exclusive OR (XOR) operation to {var} and {var}",
        r"{EXPR} : the result of applying the bitwise inclusive OR operation to {var} and {var}",
    ]:
        [x, y] = children
        env0.assert_expr_is_of_type(x, T_MathInteger_) # "bit string"
        env0.assert_expr_is_of_type(y, T_MathInteger_) # "bit string"
        return (T_MathInteger_, env0) # "bit string"

    elif p == r"{EXPR} : the 32-bit two's complement bit string representing {EX}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_MathInteger_)
        return (T_MathInteger_, env0) # bit string

    # -------------------------------------------------
    # return MathReal_ or MathInteger_ or Number or BigInt or Integer_ (arithmetic)

    elif p in [
        r'{SUM} : {TERM} {SUM_OPERATOR} {TERM}',
        r"{SUM} : {SUM} {SUM_OPERATOR} {TERM}",
        r'{PRODUCT} : {FACTOR} {PRODUCT_OPERATOR} {FACTOR}',
    ]:
        [a, op, b] = children
        (a_t, env1) = tc_expr(a, env0)
        (b_t, env2) = tc_expr(b, env1)

        if a_t.is_a_subtype_of_or_equal_to(T_ExtendedMathReal_) or b_t.is_a_subtype_of_or_equal_to(T_ExtendedMathReal_):

            if (
                T_MathPosInfinity_.is_a_subtype_of_or_equal_to(a_t)
                or
                T_MathNegInfinity_.is_a_subtype_of_or_equal_to(a_t)
            ):
                add_pass_error(a,
                    "ST includes Math-infinity, which you can't do arithmetic on"
                )
                return (T_MathReal_, env2)

            if (
                T_MathPosInfinity_.is_a_subtype_of_or_equal_to(b_t)
                or
                T_MathNegInfinity_.is_a_subtype_of_or_equal_to(b_t)
            ):
                add_pass_error(b,
                    "ST includes Math-infinity, which you can't do arithmetic on"
                )
                return (T_MathReal_, env2)

            if (
                a_t.is_a_subtype_of_or_equal_to(T_MathInteger_)
                and
                b_t.is_a_subtype_of_or_equal_to(T_MathInteger_)
                and
                op.source_text() not in ['&divide;', 'divided by', '/']
            ):
                return (T_MathInteger_, env2)
            else:
                return (T_MathReal_, env2)


        elif a_t.is_a_subtype_of_or_equal_to(T_Number) and b_t.is_a_subtype_of_or_equal_to(T_Number):

            for (x, x_t) in [(a, a_t), (b, b_t)]:
                if T_NaN_Number_.is_a_subtype_of_or_equal_to(x_t):
                    add_pass_error(x,
                        "ST includes NaN, which you can't do arithmetic on"
                    )
                #if T_InfiniteNumber_.is_a_subtype_of_or_equal_to(x_t):
                #    add_pass_error(x,
                #        "ST includes Number-infinities, which you can't do arithmetic on"
                #    )

            if (
                a_t.is_a_subtype_of_or_equal_to(T_IntegralNumber_)
                and
                b_t.is_a_subtype_of_or_equal_to(T_IntegralNumber_)
            ):
                return (T_IntegralNumber_, env2) # XXX except for division

            elif (
                a_t.is_a_subtype_of_or_equal_to(T_FiniteNumber_)
                and
                b_t.is_a_subtype_of_or_equal_to(T_FiniteNumber_)
            ):
                return (T_FiniteNumber_, env2) # unless the operands are finite-but-really-big, so their product is infinity?

            elif (
                a_t.is_a_subtype_of_or_equal_to(T_FiniteNumber_ | T_InfiniteNumber_)
                and
                b_t.is_a_subtype_of_or_equal_to(T_FiniteNumber_ | T_InfiniteNumber_)
            ):
                return (T_FiniteNumber_ | T_InfiniteNumber_, env2)

            else:
                return (T_Number, env2)

        elif a_t.is_a_subtype_of_or_equal_to(T_BigInt) and b_t.is_a_subtype_of_or_equal_to(T_BigInt):
            return (T_BigInt, env2)

        else:
            add_pass_error(expr,
                f"{a_t} and {b_t} are incompatible types for arithmetic"
            )
            assert 0, (a_t, b_t)

    elif p in [
        r"{PRODUCT} : {UNARY_OPERATOR}{FACTOR}",
    ]:
        ex = children[-1]
        (t, env1) = tc_expr(ex, env0); assert env1 is env0
        assert (
            t == T_TBD
            or
            t.is_a_subtype_of_or_equal_to(T_MathReal_)
            or
            t.is_a_subtype_of_or_equal_to(T_Number)
            or
            t.is_a_subtype_of_or_equal_to(T_BigInt)
        )
        return (t, env1)

    # -------------------------
    # return T_String

    elif p in [
        r'{LITERAL} : {STR_LITERAL}',
    ]:
        return (T_String, env0)

    elif expr.prod.lhs_s == '{STR_LITERAL}':
        return (T_String, env0)

    elif p in [
        r"{EX} : the String {var}",
        r"{EXPR} : the String value {SETTABLE}",
    ]:
        [ex] = children
        env0.ensure_expr_is_of_type(ex, T_String)
        return (T_String, env0)

    elif p in [
        r"{EXPR} : the String value consisting solely of {code_unit_lit}",
        r"{EXPR} : the String value containing only the code unit {var}",
    ]:
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_code_unit_)
        return (T_String, env1)

    elif p == r"{EXPR} : the String value that is the same as {var} except that each occurrence of {code_unit_lit} in {var} has been replaced with the six code unit sequence {STR_LITERAL}":
        [var, lita, var2, litb] = children
        assert var.children == var2.children
        env1 = env0.ensure_expr_is_of_type(var, T_String)
        return (T_String, env1)

    elif p == r"{MULTILINE_EXPR} : the string-concatenation of:{I_BULLETS}":
        [bullets] = children
        # Should check the bullets
        return (T_String, env0)

    elif p in [
        r"{EXPR} : the string-concatenation of {EX} and {EX}",
        r"{EXPR} : the string-concatenation of {EX}, {EX}, and {EX}",
        r"{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, and {EX}",
        r"{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, {EX}, and {EX}",
        r"{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, {EX}, {EX}, and {EX}",
        r"{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, and {EX}",
        r"{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, and {EX}",
        r"{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, and {EX}",
        r"{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, and {EX}",
        r"{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, and {EX}",
    ]:
        env1 = env0
        for ex in children:
            env1 = env1.ensure_expr_is_of_type(ex, T_String | T_code_unit_ | ListType(T_code_unit_))
        return (T_String, env1)

    elif p == r"{EXPR} : the String value consisting of the representation of {var} using radix {var}":
        [x_var, radix_var] = children
        env0.assert_expr_is_of_type(x_var, T_BigInt)
        env0.assert_expr_is_of_type(radix_var, T_MathInteger_)
        return (T_String, env0)

    elif p == r"{EX} : {EX} occurrences of {code_unit_lit}":
        [ex, cu_lit] = children
        env1 = env0.ensure_expr_is_of_type(ex, T_MathInteger_)
        env0.assert_expr_is_of_type(cu_lit, T_code_unit_)
        return (ListType(T_code_unit_), env1)

    elif p == r"{EXPR} : the Element Type value specified in {h_emu_xref} for {EX}":
        [emu_xref, ex] = children
        env1 = env0.ensure_expr_is_of_type(ex, T_String)
        return (T_TypedArray_element_type_, env0)

    elif p == r"{EXPR} : {var}'s {DSBN} value":
        [var, dsbn] = children
        env0.assert_expr_is_of_type(var, T_Symbol)
        assert dsbn.source_text() == '[[Description]]'
        return (T_String | T_Undefined, env0)

    elif p in [
        r"{EXPR} : the String value consisting of {EX}",
    ]:
        [ex] = children
        env1 = env0.ensure_expr_is_of_type(ex, T_code_unit_ | ListType(T_code_unit_))
        return (T_String, env1)

    elif p == r"{EXPR} : a String according to {h_emu_xref}":
        [emu_xref] = children
        return (T_String, env0)

    elif p == r"{EXPR} : the String value of the property name":
        # property of the Global Object
        # todo: make that explicit
        [] = children
        return (T_String, env0)

    elif p == r"{EXPR} : the String value formed by concatenating all the element Strings of {var} with each adjacent pair of Strings separated with {code_unit_lit}. A comma is not inserted either before the first String or after the last String":
        [var, str_literal] = children
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_String))
        return (T_String, env1)

    elif p == r"{EXPR} : the String value formed by concatenating all the element Strings of {var} with each adjacent pair of Strings separated with {var}. The {var} String is not inserted either before the first String or after the last String":
        [var, sep_var, sep_var2] = children
        assert sep_var.children == sep_var2.children
        env0.assert_expr_is_of_type(sep_var, T_String)
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_String))
        return (T_String, env1)

    elif p == r"{EXPR} : the Name of the entry in {h_emu_xref} with the Number {PP_NAMED_OPERATION_INVOCATION}":
        [emu_xref, noi] = children
        env1 = env0.ensure_expr_is_of_type(noi, T_IntegralNumber_)
        return (T_String, env1)

    elif p in [
        r"{EXPR} : the String representation of {EX}, formatted as a decimal number",
        r"{EXPR} : the String representation of {EX}, formatted as a lowercase hexadecimal number",
        r"{EXPR} : the String representation of {EX}, formatted as an uppercase hexadecimal number",
    ]:
        [ex] = children
        env1 = env0.ensure_expr_is_of_type(ex, T_Number | T_MathInteger_)
        return (T_String, env1)

    elif p == r"{EXPR} : an implementation-defined string that is either {EX} or {EXPR}":
        [exa, exb] = children
        env0.assert_expr_is_of_type(exa, T_String)
        env0.assert_expr_is_of_type(exb, T_String)
        return (T_String, env0)

    elif p == r"{EX} : an implementation-defined timezone name":
        [] = children
        return (T_String, env0)

    elif p == r"{EX} : the escape sequence for {var} as specified in the &ldquo;Escape Sequence&rdquo; column of the corresponding row":
        [var] = children
        return (T_String, env0)

    elif p == r"{EX} : the substring of {var} from {EX} to {EX}":
        [s_var, start_var, end_var] = children
        env0.assert_expr_is_of_type(s_var, T_String)
        env1 = env0.ensure_expr_is_of_type(start_var, T_MathNonNegativeInteger_)
        env2 = env1.ensure_expr_is_of_type(end_var, T_MathNonNegativeInteger_)
        return (T_String, env2)

    elif p == r"{EX} : the substring of {var} from {EX}":
        [s_var, start_var] = children
        env0.assert_expr_is_of_type(s_var, T_String)
        env0.ensure_expr_is_of_type(start_var, T_MathNonNegativeInteger_)
        return (T_String, env0)

    # ----------------------------------------------------------
    # return T_character_

    elif p == r"{EXPR} : the character matched by {PROD_REF}":
        [prod_ref] = children
        return (T_character_, env0)

    elif p == r"{EXPR} : the character whose character value is {var}":
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_MathInteger_)
        return (T_character_, env1)

    elif p == r'{EXPR} : the result of applying that mapping to {var}':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_character_)
        return (T_character_, env1)

    elif p == r'{EXPR} : the one character in CharSet {var}':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_CharSet)
        return (T_character_, env1)

    elif p == r"{EXPR} : the character {SETTABLE}":
        [settable] = children
        env1 = env0.ensure_expr_is_of_type(settable, T_character_)
        return (T_character_, env1)

    # ----------------------------------------------------------
    # return T_code_unit_

    elif expr.prod.lhs_s == '{code_unit_lit}':
        return (T_code_unit_, env0)

    elif p == r"{EXPR} : {var}'s single code unit element": # todo: element of String
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_String)
        return (T_code_unit_, env1)

    elif p == r'{EX} : the first code unit of {var}':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_String)
        return (T_code_unit_, env1)

    elif p == r"{EX} : the code unit whose value is determined by {PROD_REF} according to {h_emu_xref}":
        [nonterminal, emu_xref] = children
        return (T_code_unit_, env0)

    elif p in [
        r"{EX} : the code unit whose value is {EX}",
    ]:
        [ex] = children
        env1 = env0.ensure_expr_is_of_type(ex, T_MathInteger_ | T_MathInteger_)
        return (T_code_unit_, env0)

    elif p == r"{EXPR} : the code unit whose numeric value is that of {EXPR}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_code_point_)
        return (T_code_unit_, env0)

    elif p == r"{EXPR} : the code unit whose numeric value is {EX}":
        [ex] = children
        env0.assert_expr_is_of_type(ex, T_MathNonNegativeInteger_)
        return (T_code_unit_, env0)

    # ----

    elif p == r"{EX} : the code unit at index {EX} within {EX}":
        [index_ex, str_ex] = children
        env0.assert_expr_is_of_type(str_ex, T_String)
        env1 = env0.ensure_expr_is_of_type(index_ex, T_MathInteger_)
        return (T_code_unit_, env1)

    # ----------------------------------------------------------
    # return T_code_point_

    elif p in [
        r"{EXPR} : the code point {var}",
        # This means "the code point whose numeric value is {var}"
        r"{EXPR} : the code point whose numeric value is {NAMED_OPERATION_INVOCATION}",
    ]:
        [var] = children
        env0.assert_expr_is_of_type(var, T_MathInteger_)
        return (T_code_point_, env0)

    elif p == r"{EXPR} : the code point whose numeric value is that of {var}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_code_unit_)
        return (T_code_point_, env0)

    elif expr.prod.lhs_s == '{code_point_lit}':
        return (T_code_point_, env0)

    elif p in [
        r"{EX} : the code point matched by {PROD_REF}",
    ]:
        [nont] = children
        return (T_code_point_, env0)

    elif p == r"{EX} : the single code point matched by this production":
        [] = children
        return (T_code_point_, env0)

    # ----------------------------------------------------------
    # return T_Unicode_code_points_

    elif p == r'{EXPR} : the source text that was recognized as {PROD_REF}':
        [nonterminal] = children
        # XXX Should check whether nonterminal makes sense
        # with respect to the emu-grammar accompanying this alg/expr.
        return (T_Unicode_code_points_, env0)

    elif p == r"{EXPR} : the source text matched by {PROD_REF}":
        [nont] = children
        return (T_Unicode_code_points_, env0) # XXX spec bug: needs to be T_String?

    elif p == r"{EXPR} : the result of toLowercase({var}), according to the Unicode Default Case Conversion algorithm":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Unicode_code_points_)
        return (T_Unicode_code_points_, env0)

    elif p == r"{EXPR} : the result of toUppercase(&laquo; {var} &raquo;), according to the Unicode Default Case Conversion algorithm":
        [var] = children
        env0.assert_expr_is_of_type(var, T_code_point_)
        return (T_Unicode_code_points_, env0)

    elif p == r"{EXPR} : the sequence of code points resulting from interpreting each of the 16-bit elements of {var} as a Unicode BMP code point. UTF-16 decoding is not applied to the elements":
        [var] = children
        env0.assert_expr_is_of_type(var, T_String)
        return (T_Unicode_code_points_, env0)

    # ----------------------------------------------------------
    # return ListType

    # --------------------
    # ListType(T_MathInteger_)

    elif (
        p.startswith(r'{EXPR} : a List whose elements are the 4 bytes that are the result of converting {var} to IEEE 754-2019 binary32 format')
        or
        p.startswith(r'{EXPR} : a List whose elements are the 8 bytes that are the IEEE 754-2019 binary64 format encoding of {var}.')
    ):
        var = children[0]
        env1 = env0.ensure_expr_is_of_type(var, T_Number)
        return (ListType(T_MathInteger_), env1)

    elif p in [
        r'{EXPR} : a List whose elements are the {var}-byte binary encoding of {var}. If {var} is {LITERAL}, the bytes are ordered in big endian order. Otherwise, the bytes are ordered in little endian order',
        r"{EXPR} : a List whose elements are the {var}-byte binary two's complement encoding of {var}. If {var} is {LITERAL}, the bytes are ordered in big endian order. Otherwise, the bytes are ordered in little endian order",
    ]:
        [n_var, v_var, i_var, literal] = children
        env0.assert_expr_is_of_type(n_var, T_MathNonNegativeInteger_)
        env0.assert_expr_is_of_type(v_var, T_MathNonNegativeInteger_)
        env0.assert_expr_is_of_type(i_var, T_Boolean)
        env0.assert_expr_is_of_type(literal, T_Boolean)
        return (ListType(T_MathInteger_), env0)

    elif p == r"{EXPR} : a List of length {var} whose elements are nondeterministically chosen byte values":
        [var] = children
        env0.assert_expr_is_of_type(var, T_MathInteger_)
        return (ListType(T_MathInteger_), env0)

    elif p == r"{EXPR} : a List of length {var} whose elements are the sequence of {var} bytes starting with {var}[{var}]":
        [var1, var2, var3, var4] = children
        assert var1.children == var2.children
        env0.assert_expr_is_of_type(var1, T_MathInteger_)
        env1 = env0.ensure_expr_is_of_type(var3, T_Data_Block | T_Shared_Data_Block)
        env0.assert_expr_is_of_type(var4, T_MathInteger_)
        return (ListType(T_MathInteger_), env1)

    elif p == r"{EXPR} : the List of octets resulting by applying the UTF-8 transformation to {DOTTING}":
        [dotting] = children
        env1 = env0.ensure_expr_is_of_type(dotting, T_code_point_)
        return (ListType(T_MathInteger_), env1)

    # ----------------------
    # ListType(T_code_unit_)

    elif p in [
        r"{EXPR} : a List whose elements are the code units that are the elements of {var}",
        r"{EXPR} : a List consisting of the sequence of code units that are the elements of {var}",
    ]:
        [var] = children
        env0.assert_expr_is_of_type(var, T_String)
        return (ListType(T_code_unit_), env0)

    # ---------------
    # ListType(T_String)

    # ---------------
    # ListType(other)

    elif p == r'{EXPR} : a new empty List':
        [] = children
        return (T_List, env0) # (ListType(T_0), env0)

    elif p in [
        r"{EXPR} : a List whose sole element is {EX}",
    ]:
        [element_expr] = children
        (element_type, env1) = tc_expr(element_expr, env0); assert env1.equals(env0)
        return (ListType(element_type), env0)

    elif p in [
        r"{EXPR} : the list-concatenation of {EX} and {EX}",
    ]:
        [var, noi] = children
        (t1, env1) = tc_expr(var, env0); assert env1 is env0
        (t2, env2) = tc_expr(noi, env0); assert env2 is env0
        if t1 == T_TBD and t2 == T_TBD:
            list_type = T_List
        elif t1 == T_TBD and (t2 == T_List or isinstance(t2, ListType)):
            list_type = t2
        elif t2 == T_TBD and (t1 == T_List or isinstance(t1, ListType)):
            list_type = t1

        elif isinstance(t1, ListType) and t2 == T_List:
            list_type = t1

        elif isinstance(t1, ListType) and isinstance(t2, ListType):
            if t1.is_a_subtype_of_or_equal_to(t2):
                list_type = t2
            elif t2.is_a_subtype_of_or_equal_to(t1):
                list_type = t1
            else:
                assert 0
        else:
            assert 0
            # assert t1.element_type == t2.element_type
        return (list_type, env0)

    elif p == r"{EXPR} : the list-concatenation of {var}, {var}, and {var}":
        [exa, exb, exc] = children
        # kludge
        if exa.source_text() == '_names1_':
            et = T_String
        elif exa.source_text() == '_declarations1_':
            et = T_Parse_Node
        else:
            assert 0, exa
        lt = ListType(et)
        env1 = env0.ensure_expr_is_of_type(exa, lt)
        env2 = env1.ensure_expr_is_of_type(exb, lt)
        env3 = env2.ensure_expr_is_of_type(exc, lt)
        return (lt, env3)

    elif p == r'{EXPR} : a List whose elements are the elements of {var} ordered as if an Array of the same values had been sorted using {percent_word} using {LITERAL} as {var}':
        [var, _, _, _] = children
        (t, env1) = tc_expr(var, env0); assert env1 is env0
        assert t.is_a_subtype_of_or_equal_to(T_List)
        return (t, env0)

    elif p == r"{EXPR} : the List of {nonterminal} items in {PROD_REF}, in source text order":
        [nont, prod_ref] = children
        return (ListType(T_Parse_Node), env0)

    elif p == r"{EXPR} : the List of arguments that was passed to this function by {dsb_word} or {dsb_word}":
        [dsbwa, dsbwb] = children
        assert dsbwa.source_text() == '[[Call]]'
        assert dsbwb.source_text() == '[[Construct]]'
        return (ListType(T_Tangible_), env0)

    elif p == r"{EXPR} : {var}<sup>th</sup> element of {var}'s _captures_ List":
        [n_var, state_var] = children
        env0.assert_expr_is_of_type(n_var, T_MathInteger_)
        env0.assert_expr_is_of_type(state_var, T_State)
        return (T_captures_entry_, env0)

    elif p == r"{EXPR} : a List of {EX} {LITERAL} values, indexed 1 through {EX}":
        [var, literal, var2] = children
        assert var.source_text() == var2.source_text()
        env0.assert_expr_is_of_type(var, T_MathInteger_)
        (lit_t, env1) = tc_expr(literal, env0); assert env1 is env0
        return (ListType(lit_t), env1)

    elif p == r"{EX} : {var}'s _input_":
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_State)
        return (ListType(T_character_), env1)

    elif p == r"{EXPR} : a List whose elements are bytes from {var} at indices {var} (inclusive) through {EX} (exclusive)":
        [data_var, lo_var, hi_ex] = children
        env1 = env0.ensure_expr_is_of_type(data_var, T_Data_Block | T_Shared_Data_Block)
        env1.assert_expr_is_of_type(lo_var, T_MathNonNegativeInteger_)
        env1.assert_expr_is_of_type(hi_ex, T_MathNonNegativeInteger_)
        return (ListType(T_MathNonNegativeInteger_), env1)

    elif p == r"{EXPR} : a List containing the names of all the internal slots that {h_emu_xref} requires for the built-in function object that is about to be created":
        [xref] = children
        return (ListType(T_SlotName_), env0)

    # --------------------------------------------------------
    # return T_Parse_Node

    elif p == r"{EXPR} : the {nonterminal} that is covered by {LOCAL_REF}":
        [nonterminal, local_ref] = children
        env0.assert_expr_is_of_type(local_ref, T_Parse_Node)
        return (ptn_type_for(nonterminal), env0)

    # ----

    elif p in [
        r"{PROD_REF} : the {nonterminal} of {LOCAL_REF}",
    ]:
        [nonterminal, var] = children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        # XXX could check that t is a nonterminal that actually has a child of that type
        # but that requires having the whole grammar handy
        return (ptn_type_for(nonterminal), env0)

    elif p == r'{PROD_REF} : this {nonterminal}':
        [nonterminal] = children
        # XXX check
        return (ptn_type_for(nonterminal), env0)

    elif p == r'{PROD_REF} : {nonterminal}':
        [nonterminal] = children
        return (ptn_type_for(nonterminal), env0)

    elif p == r"{PROD_REF} : {nonterminal} {var}":
        [nonterminal, var] = children
        t = ptn_type_for(nonterminal)
        env0.assert_expr_is_of_type(var, t)
        return (t, env0)

    elif p == r'{PROD_REF} : the {ORDINAL} {nonterminal}':
        [ordinal, nonterminal] = children
        # XXX should check that the 'current' production has such.
        return (ptn_type_for(nonterminal), env0)

    elif p in [
        r'{PROD_REF} : the {nonterminal}',
    ]:
        nonterminal = children[-1]
        return (ptn_type_for(nonterminal), env0)

    elif p == r"{PROD_REF} : that {nonterminal}":
        [nont] = children
        return (ptn_type_for(nont), env0)

    elif p == r"{EXPR} : an instance of the production {h_emu_grammar}":
        [emu_grammar] = children
        assert emu_grammar.source_text() == '<emu-grammar>FormalParameters : [empty]</emu-grammar>'
        return (ptn_type_for('FormalParameters'), env0)

    elif p == r"{EXPR} : the {nonterminal}, {nonterminal}, or {nonterminal} that most closely contains {var}":
        [*nont_, var] = children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        return (T_Parse_Node, env0)

    elif p == r"{EXPR} : the Parse Node (an instance of {var}) at the root of the parse tree resulting from the parse":
        [var] = children
        env0.assert_expr_is_of_type(var, T_grammar_symbol_)
        return (T_Parse_Node, env0)

    elif p in [
        r"{PROD_REF} : this phrase",
        r"{PROD_REF} : this production",
    ]:
        return (T_Parse_Node, env0)

    elif p in [
        r"{PROD_REF} : the derived {nonterminal}",
    ]:
        [nont] = children
        return (T_Parse_Node, env0)

    elif p == r"{PROD_REF} : the {nonterminal} containing {LOCAL_REF}":
        [nonta, local_ref] = children
        return (T_Parse_Node, env0)

    # --------------------------------------------------------
    # return T_Object

    elif p == r'{EXPR} : a newly created object with an internal slot for each name in {var}':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_SlotName_))
        return (T_Object, env1)

    elif p in [
        r"{LITERAL} : {percent_word}",
    ]:
        [percent_word] = children
        pws = percent_word.source_text()
        if pws in [
            '%Promise%',
            '%RegExp%',
            '%ArrayBuffer%',
            '%SharedArrayBuffer%',
        ]:
            rt = T_constructor_object_
        else:
            rt = T_Object
        return (rt, env0)
        # We could be more specific in many cases, but I'm not sure it would make any difference.

    elif p == r"{EXPR} : {var}'s intrinsic object named {var}":
        [r_var, n_var] = children
        env0.assert_expr_is_of_type(r_var, T_Realm_Record)
        env0.assert_expr_is_of_type(n_var, T_String)
        return (T_Object, env0)

    # -------------------------------------------------
    # return T_CharSet

    elif p == r'{EXPR} : the CharSet containing all characters with a character value greater than or equal to {var} and less than or equal to {var}':
        [var1, var2] = children
        env1 = env0.ensure_expr_is_of_type(var1, T_MathInteger_)
        env2 = env0.ensure_expr_is_of_type(var2, T_MathInteger_)
        assert env1 is env0
        assert env2 is env0
        return (T_CharSet, env0)

    elif p in [
        r"{EXPR} : the CharSet containing the single character {code_point_lit}",
        r"{EXPR} : the CharSet containing the single character {var}",
    ]:
        [ex] = children
        env0.ensure_expr_is_of_type(ex, T_character_)
        return (T_CharSet, env0)

    elif p == r"{EXPR} : the CharSet containing the character matched by {PROD_REF}":
        [prod_ref] = children
        return (T_CharSet, env0)

    elif p == r"{EXPR} : a one-element CharSet containing the character {var}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_character_)
        return (T_CharSet, env0)

    elif p == r"{EXPR} : the union of CharSets {var}, {var} and {var}":
        [va, vb, vc] = children
        enva = env0.ensure_expr_is_of_type(va, T_CharSet)
        envb = env0.ensure_expr_is_of_type(vb, T_CharSet)
        envc = env0.ensure_expr_is_of_type(vc, T_CharSet)
        return (T_CharSet, envs_or([enva, envb, envc]))

    elif p in [
        r"{EXPR} : the union of {var} and {var}",
        r"{EXPR} : the union of CharSets {var} and {var}",
    ]:
        [va, vb] = children
        enva = env0.ensure_expr_is_of_type(va, T_CharSet)
        envb = env0.ensure_expr_is_of_type(vb, T_CharSet)
        return (T_CharSet, env_or(enva, envb))

    elif p == r"{EXPR} : the CharSet of all characters":
        [] = children
        return (T_CharSet, env0)

    elif p == r"{EXPR} : the ten-element CharSet containing the characters `0` through `9` inclusive":
        [] = children
        return (T_CharSet, env0)

    elif p == r"{EXPR} : the CharSet containing every character in {STR_LITERAL}":
        [strlit] = children
        return (T_CharSet, env0)

    elif p == r"{EXPR} : the CharSet containing all characters not in {NAMED_OPERATION_INVOCATION}":
        [noi] = children
        env0.assert_expr_is_of_type(noi, T_CharSet)
        return (T_CharSet, env0)

    elif p == r"{EXPR} : the CharSet containing all characters corresponding to a code point on the right-hand side of the {nonterminal} or {nonterminal} productions":
        [nont1, nont2] = children
        return (T_CharSet, env0)

    elif p == r"{EXPR} : the empty CharSet":
        [] = children
        return (T_CharSet, env0)

    elif p == r"{EXPR} : the CharSet containing all Unicode code points whose character database definition includes the property {var} with value {var}":
        [va, vb] = children
        env0.assert_expr_is_of_type(va, ListType(T_code_point_))
        env0.assert_expr_is_of_type(vb, ListType(T_code_point_))
        return (T_CharSet, env0)

    elif p == r"{EXPR} : the CharSet containing all Unicode code points whose character database definition includes the property &ldquo;General_Category&rdquo; with value {var}":
        [v] = children
        env0.assert_expr_is_of_type(v, ListType(T_code_point_))
        return (T_CharSet, env0)

    elif p == r"{EXPR} : the CharSet containing all Unicode code points whose character database definition includes the property {var} with value &ldquo;True&rdquo;":
        [v] = children
        env0.assert_expr_is_of_type(v, ListType(T_code_point_))
        return (T_CharSet, env0)

    elif p in [
        r"{EXPR} : the CharSet containing all Unicode code points included in {NAMED_OPERATION_INVOCATION}",
        r"{EXPR} : the CharSet containing all Unicode code points not included in {NAMED_OPERATION_INVOCATION}",
    ]:
        [noi] = children
        env0.assert_expr_is_of_type(noi, T_CharSet)
        return (T_CharSet, env0)

    elif p == r"{EXPR} : the CharSet containing all characters {var} such that {var} is not in {var} but {NAMED_OPERATION_INVOCATION} is in {var}":
        [loop_var, loop_var2, cs_var, noi, cs_var2] = children
        assert loop_var.source_text() == loop_var2.source_text()
        assert cs_var.source_text() == cs_var2.source_text()
        env0.assert_expr_is_of_type(cs_var, T_CharSet)
        env1 = env0.plus_new_entry(loop_var, T_character_)
        env1.assert_expr_is_of_type(noi, T_character_)
        return (T_CharSet, env0)

    elif p == r"{NAMED_OPERATION_INVOCATION} : the CharSet returned by {h_emu_grammar}":
        [emu_grammar] = children
        return (T_CharSet, env0)

    # -------------------------------------------------
    # return T_function_object_

    elif p == r'{EXPR} : a new built-in function object that, when called, performs the action described by {var} using the provided arguments as the values of the corresponding parameters specified by {var}. The new function object has internal slots whose names are the elements of {var}, and an {DSBN} internal slot':
        [var1, var2, var3, dsbn] = children
        env1 = env0.ensure_expr_is_of_type(var1, T_proc_ | T_alg_steps)
        # env1 = env0.ensure_expr_is_of_type(var2, )
        return (T_function_object_, env1)

    # ------------------------------------------------
    # return T_alg_steps

    elif p == r"{EXPR} : the algorithm steps defined in {h_emu_xref}":
        [emu_xref] = children
        return (T_alg_steps, env0)

    # ------------------------------------------------
    # return T_execution_context

    elif p == r"{EXPR} : a new execution context":
        [] = children
        return (T_execution_context, env0)

    elif p == r"{EXPR} : a new ECMAScript code execution context":
        [] = children
        return (T_execution_context, env0)

    elif p == r'{EXPR} : the running execution context':
        [] = children
        return (T_execution_context, env0)

    elif p == r'{EXPR} : the topmost execution context on the execution context stack whose ScriptOrModule component is not {LITERAL}':
        [literal] = children
        return (T_execution_context, env0)

    elif p == r"{EXPR} : the second to top element of the execution context stack":
        [] = children
        return (T_execution_context, env0)

    # -------------------------------------------------

    elif p in [
        r"{EXPR} : the value currently bound to {var} in {var}",
        r"{SETTABLE} : the bound value for {var} in {var}",
    ]:
        [n_var, er_var] = children
        env0.assert_expr_is_of_type(n_var, T_String)
        env0.assert_expr_is_of_type(er_var, T_Environment_Record)
        return (T_Tangible_, env0)

    elif p == r"{EXPR} : the Completion Record that is the result of evaluating {var} in a manner that conforms to the specification of {var}. {var} is the *this* value, {var} provides the named parameters, and the NewTarget value is *undefined*":
        [avar, bvar, cvar, dvar] = children
        assert avar.children == bvar.children
        env0.assert_expr_is_of_type(avar, T_function_object_)
        env0.assert_expr_is_of_type(cvar, T_Tangible_)
        env0.assert_expr_is_of_type(dvar, ListType(T_Tangible_))
        return (T_Tangible_ | T_throw_, env0)

    elif p == r"{EXPR} : the Completion Record that is the result of evaluating {var} in a manner that conforms to the specification of {var}. The *this* value is uninitialized, {var} provides the named parameters, and {var} provides the NewTarget value":
        [avar, bvar, cvar, dvar] = children
        assert avar.children == bvar.children
        env0.assert_expr_is_of_type(avar, T_function_object_)
        env0.assert_expr_is_of_type(cvar, ListType(T_Tangible_))
        env0.assert_expr_is_of_type(dvar, T_Tangible_)
        return (T_Tangible_ | T_throw_, env0)

    # -------------------------------------------------
    # return component of T_execution_context

    elif p in [
        r"{SETTABLE} : the {EXECUTION_CONTEXT_COMPONENT} component of {var}",
        r"{SETTABLE} : The {EXECUTION_CONTEXT_COMPONENT} of {var}",
        r"{SETTABLE} : the {EXECUTION_CONTEXT_COMPONENT} of {var}",
        r"{SETTABLE} : {var}'s {EXECUTION_CONTEXT_COMPONENT}",
    ]:
        if p.endswith('{var}'):
            [component_name, var] = children
        else:
            [var, component_name] = children

        component_name = component_name.source_text()

        # env0.assert_expr_is_of_type(var, T_execution_context)

        (t, env1) = tc_expr(var, env0); assert env1 is env0
        if t == T_TBD:
            t = T_execution_context
            env2 = env1.with_expr_type_replaced(var, t)
        else:
            env2 = env1

        result_type = {
            # todo: make it a record?
            # 7110: Table 22: State Components for All Execution Contexts
            'code evaluation state': T_host_defined_,
            'Function'      : T_function_object_,
            'Realm'         : T_Realm_Record,
            'ScriptOrModule': T_Module_Record | T_Script_Record,

            # 7159: Table 23: Additional State Components for ECMAScript Code Execution Contexts
            'LexicalEnvironment' : T_Environment_Record,
            'VariableEnvironment': T_Environment_Record,
            'PrivateEnvironment' : T_PrivateEnvironment_Record,

            # 7191: Table 24: Additional State Components for Generator Execution Contexts
            'Generator' : T_Object,
        }[component_name]

        return (result_type, env2)

    # -------------------------------------------------
    # return proc type

    elif p == r'{EXPR} : the abstract operation named in the Conversion Operation column in {h_emu_xref} for Element Type {var}':
        [emu_xref, var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_TypedArray_element_type_)
        return (ProcType([T_Tangible_], T_IntegralNumber_), env1)

    elif p == r"{MULTILINE_EXPR} : a new {CLOSURE_KIND} with {CLOSURE_PARAMETERS} that captures {CLOSURE_CAPTURES} and performs the following {CLOSURE_STEPS} when called:{IND_COMMANDS}":
        [clo_kind, clo_parameters, clo_captures, _, commands] = children
        clo_kind = clo_kind.source_text()

        #XXX Should assert no intersection between clo_parameters and clo_captures

        # -----

        env_for_commands = Env()

        n_parameters = len(clo_parameters.children)
        if clo_kind == 'Abstract Closure':
            clo_param_types = [T_TBD] * n_parameters
        elif clo_kind == 'Continuation':
            assert n_parameters == 1
            clo_param_types = [T_State]
        elif clo_kind == 'Matcher':
            assert n_parameters == 2
            clo_param_types = [T_State, T_Continuation]
        elif clo_kind == 'Job Abstract Closure':
            assert n_parameters == 0
            clo_param_types = []
        elif clo_kind == 'read-modify-write modification function':
            assert n_parameters == 2
            clo_param_types = [ListType(T_MathInteger_), ListType(T_MathInteger_)]
        else:
            assert 0, clo_kind

        for (clo_param_var, clo_param_type) in zip(clo_parameters.children, clo_param_types):
            env_for_commands = env_for_commands.plus_new_entry(clo_param_var, clo_param_type)

        for clo_capture_var in clo_captures.children:
            clo_capture_type = env0.lookup(clo_capture_var)
            env_for_commands = env_for_commands.plus_new_entry(clo_capture_var, clo_capture_type)

        env_for_commands.vars['*return*'] = T_0

        # -----

        defns = [(None, commands)]
        env_after_commands = tc_proc(None, defns, env_for_commands)
        t = ProcType(clo_param_types, env_after_commands.vars['*return*'])
        return (t, env0)

    # -------------------------------------------------
    # return Environment_Record

    elif p in [
        r'{EXPR} : a new {ENVIRONMENT_RECORD_KIND} Environment Record containing no bindings',
        r'{EXPR} : a new {ENVIRONMENT_RECORD_KIND} Environment Record',
    ]:
        [kind] = children
        t = type_for_environment_record_kind(kind)
        return (t, env0)

    # -------------------------------------------------
    # return T_Realm_Record

    elif p == r'{EX} : the current Realm Record':
        [] = children
        return (T_Realm_Record, env0)

    elif p == r"{EXPR} : a new Realm Record":
        [] = children
        return (T_Realm_Record, env0)

    # -------------------------------------------------
    # whatever

    elif expr.prod.lhs_s == "{nonterminal}":
        nont_name = expr.source_text()[1:-1]
        # Note that |Foo| often denotes a Parse Node,
        # rather than a grammar symbol,
        # but we capture those cases before they can get to here.
        return (T_grammar_symbol_, env0)

    elif p == r"{EXPR} : the grammar symbol {nonterminal}":
        [nont] = children
        return (T_grammar_symbol_, env0)

    elif p in [
        r"{G_SYM} : {nonterminal}",
        r"{G_SYM} : {TERMINAL}",
    ]:
        return (T_grammar_symbol_, env0)

    elif expr.prod.lhs_s == '{var}':
        [var_name] = children
        return (env0.vars[var_name], env0)

    elif p in [
        r'{SETTABLE} : {var}',
    ]:
        [var] = children
        [var_name] = var.children
        if var_name not in env0.vars:
            add_pass_error(
                var,
                "NOT DEFINED"
            )
            t = T_TBD
        else:
            t = env0.vars[var_name]
            # print("the type of %s is %s" % (var_name, t))
        return (t, env0)

    elif p in [
        r'{EXPR} : the Agent Record of the surrounding agent',
        r"{EXPR} : the surrounding agent's Agent Record",
    ]:
        [] = children
        return (T_Agent_Record, env0)

    elif p == r'{EXPR} : a new Data Block value consisting of {var} bytes. If it is impossible to create such a Data Block, throw a {ERROR_TYPE} exception':
        [var, error_type] = children
        (t, env1) = tc_expr(var, env0)
        assert env1 is env0
        assert t.is_a_subtype_of_or_equal_to(T_MathInteger_)
        proc_add_return(env0, ThrowType(type_for_ERROR_TYPE(error_type)), error_type)
        return (T_Data_Block, env1)

    elif p == r'{EXPR} : a new Shared Data Block value consisting of {var} bytes. If it is impossible to create such a Shared Data Block, throw a {ERROR_TYPE} exception':
        [var, error_type] = children
        (t, env1) = tc_expr(var, env0)
        assert env1 is env0
        assert t.is_a_subtype_of_or_equal_to(T_MathInteger_)
        proc_add_return(env0, ThrowType(type_for_ERROR_TYPE(error_type)), error_type)
        return (T_Shared_Data_Block, env1)

    elif p == '{RECORD_CONSTRUCTOR} : {RECORD_CONSTRUCTOR_PREFIX} { {FIELDS} }':
        [record_constructor_prefix, fields] = children
        constructor_prefix = record_constructor_prefix.source_text().replace('the ', '')

        if constructor_prefix == 'Completion Record':
            f_ = dict( get_field_items(fields) )
            assert sorted(f_.keys()) == ['Target', 'Type', 'Value']
            type_ex = f_['Type']
            value_ex = f_['Value']
            target_ex = f_['Target']

            if fields.source_text() == '[[Type]]: _completionRecord_.[[Type]], [[Value]]: _value_, [[Target]]: _completionRecord_.[[Target]]':
                # The specialest of special cases!
                # Occurs once, in UpdateEmpty.
                # In the context there,
                # the static type of _completionRecord_ is
                # (or would be, if STA were smart enough)
                # T_empty_ | T_continue_ | T_break_,
                # and the static type of _value_ is T_Tangible_ | T_empty_

                return (T_Tangible_ | T_empty_ | T_continue_ | T_break_, env0)

            else:
                env1 = env0.ensure_expr_is_of_type(value_ex, T_Tangible_ | T_empty_)
                (value_type, _) = tc_expr(value_ex, env1) # bleah

                env0.assert_expr_is_of_type(target_ex, T_String | T_empty_)

                ct = type_corresponding_to_comptype_literal(type_ex)
                if ct == T_Normal:
                    t = value_type
                elif ct == T_throw_:
                    t = ThrowType(value_type)
                else:
                    t = ct

                return (t, env1)

        if constructor_prefix == 'Record':
            record_type_name = None
            field_names = sorted(get_field_names(fields))
            if field_names == ['Array', 'Site']:
                record_type_name = 'templateMap_entry_'
            elif field_names == ['Closure', 'Key']:
                record_type_name = 'methodDef_record_'
            elif field_names == ['Configurable', 'Enumerable', 'Get', 'Set', 'Value', 'Writable']:
                # CompletePropertyDescriptor: the almost-Property Descriptor
                record_type_name = 'Property Descriptor'
            elif field_names == ['ExportName', 'Module']:
                record_type_name = 'ExportResolveSet_Record_'
            elif field_names == ['Key', 'Symbol']:
                record_type_name = 'GlobalSymbolRegistry Record'
            elif field_names == ['Key', 'Value']:
                record_type_name = 'MapData_record_'
            elif field_names == ['Reject', 'Resolve']:
                record_type_name = 'ResolvingFunctions_record_'
            elif field_names == ['CodePoint', 'CodeUnitCount', 'IsUnpairedSurrogate']:
                record_type_name = 'CodePointAt_record_'
            elif field_names == ['HeldValue', 'UnregisterToken', 'WeakRefTarget']:
                record_type_name = 'FinalizationRegistryCellRecord_'
            elif field_names == ['Greedy', 'Max', 'Min']:
                record_type_name = 'QuantifierResultRecord_'
            elif field_names == ['Max', 'Min']:
                record_type_name = 'QuantifierPrefixResultRecord_'
            elif field_names == ['CharSet', 'Invert']:
                record_type_name = 'CharacterClassResultRecord_'
            elif field_names == ['Job', 'Realm']:
                record_type_name = 'Job_record_'

            elif field_names == ['Value']:
                fst = fields.source_text()
                if fst == '[[Value]]: *false*':
                    record_type_name = 'boolean_value_record_'
                elif fst == '[[Value]]: 1':
                    record_type_name = 'integer_value_record_'
                else:
                    assert 0, fst

            if record_type_name:
                add_pass_error(
                    expr,
                    "Inferred record type `%s`: be explicit!" % record_type_name
                )
                field_info = fields_for_record_type_named_[record_type_name]
            else:
                add_pass_error(
                    expr,
                    "Could not infer a record type for fields: " + str(field_names)
                )
                record_type_name = 'Record'
                field_info = None

        else:
            if constructor_prefix in [
                'ReadModifyWriteSharedMemory',
                'ReadSharedMemory',
                'WriteSharedMemory',
            ]:
                record_type_name = constructor_prefix + ' event'
            elif constructor_prefix in [
                'PromiseReaction',
                'PromiseCapability',
                'AsyncGeneratorRequest',
            ]:
                record_type_name = constructor_prefix + ' Record'
            elif constructor_prefix == 'PropertyDescriptor':
                record_type_name = 'Property Descriptor'
            else:
                record_type_name = constructor_prefix
            field_info = fields_for_record_type_named_[record_type_name]

        envs = []
        for (dsbn_name, ex) in get_field_items(fields):
            if field_info is None:
                # (because it's just a Record, not a particular (named) kind of Record)
                # We can't really assert anything.
                (t, env1) = tc_expr(ex, env0); assert env1 is env0
            else:
                declared_field_type = field_info[dsbn_name]
                # If the constructor referred to an undeclared field, that would raise a KeyError
                env1 = env0.ensure_expr_is_of_type(ex, declared_field_type)
            envs.append(env1)
        env2 = envs_or(envs)

        # XXX: Should also ensure that each declared field is specified exactly once.

        return ( NamedType(record_type_name), env2 )

    elif p == r'{EXPR} : an Iterator object ({h_emu_xref}) whose `next` method iterates over all the String-valued keys of enumerable properties of {var}. The iterator object is never directly accessible to ECMAScript code. The mechanics and order of enumerating the properties is not specified but must conform to the rules specified below':
        [emu_xref, var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_Object)
        return (T_Iterator_object_, env1)

    elif p == r"{PP_NAMED_OPERATION_INVOCATION} : {NAMED_OPERATION_INVOCATION}":
        [noi] = children
        (noi_t, env1) = tc_expr(noi, env0, expr_value_will_be_discarded)
        if noi_t == T_TBD:
            # Don't do the comparison to Normal,
            # because that loses the TBD-ness,
            # which is used as a sentinel all over.
            return (noi_t, env1)
        else:
            # (normal_part_of_type, abrupt_part_of_type) = noi_t.split_by(T_Normal)
            # if abrupt_part_of_type != T_0:
            #     add_pass_error(
            #         expr,
            #         "warning: `%s` static type includes `%s`, but isn't prefixed by ! or ?"
            #         % (expr.source_text(), abrupt_part_of_type)
            #     )
            #     # But that might be okay.
            #     # E.g. Return {NAMED_OPERATION_INVOCATION} -- inserting a '?' would have no effect.
            #     # or if next instruction is ReturnIfAbrupt.
            #     # So I dropped this warning,
            #     # and just rely on Abrupt values being flagged if necessary down the line.
            return (noi_t, env1)

    elif p == r'{PP_NAMED_OPERATION_INVOCATION} : ! {NAMED_OPERATION_INVOCATION}':
        [noi] = children
        (noi_t, env1) = tc_expr(noi, env0)

        if noi_t == T_TBD:
            return (T_TBD, env1)

        (abrupt_part_of_type, normal_part_of_type) = noi_t.split_by(T_Abrupt)

        if abrupt_part_of_type == T_0:
            # add_pass_error(
            #     noi,
            #     "The static type of the invocation is `%s`, so shouldn't need a '!'" % str(noi_t)
            # )
            # There are a lot of these now, and it's only goig to increase.
            pass
        else:
            # add_pass_error(
            #     expr,
            #     "STA fails to confirm that `%s` will return a Normal" % noi.source_text()
            # )
            # It's unsurprising, perhaps even *expected*,
            # that STA can't confirm it.
            pass

        return (normal_part_of_type, env1)

    elif p in [
        r'{PP_NAMED_OPERATION_INVOCATION} : ? {NAMED_OPERATION_INVOCATION}',
        r"{EX} : ? {DOTTING}",
        r"{EX} : ? {var}",
    ]:
        [operand] = children
        (operand_t, env1) = tc_expr(operand, env0)

        if operand_t == T_TBD:
            return (T_TBD, env1)

        (abrupt_part_of_type, normal_part_of_type) = operand_t.split_by(T_Abrupt)

        if normal_part_of_type == T_0:
            add_pass_error(
                expr,
                "used '?', but STA says operation can't return normal: " + expr.source_text()
            )

        if abrupt_part_of_type == T_0:
            add_pass_error(
                expr,
                "used '?', but STA says operation can't return abrupt: " + expr.source_text()
            )

        proc_add_return(env1, abrupt_part_of_type, expr)

        # RequireInternalSlot is a quasi-type-test.
        env2 = env1
        if str(operand.prod) == '{NAMED_OPERATION_INVOCATION} : {PREFIX_PAREN}':
            [pp] = operand.children
            assert str(pp.prod).startswith(r'{PREFIX_PAREN} : {OPN_BEFORE_PAREN}({EXLIST_OPT})')
            [opn_before_paren, exlist_opt] = pp.children[0:2]
            if opn_before_paren.source_text() == 'RequireInternalSlot':
                # This amounts to a type-test.
                # I.e., in the not-returning-early env resulting from this NAMED_OPERATION_INVOCATION,
                # we can narrow the type of the first arg to RequireInternalSlot.
                (obj_arg, slotname_arg) = exes_in_exlist_opt(exlist_opt)
                env2 = env1.with_expr_type_narrowed(obj_arg, T_Object)
                # XXX Depending on the slotname_arg, we could narrow it further.

        return (normal_part_of_type, env2)

    elif p in [
        r"{SETTABLE} : the running execution context's {EXECUTION_CONTEXT_COMPONENT}",
        r"{SETTABLE} : the {EXECUTION_CONTEXT_COMPONENT} of the running execution context",
    ]:
        [component_name] = children
        t = {
            'LexicalEnvironment' : T_Environment_Record,
            'VariableEnvironment': T_Environment_Record,
            'PrivateEnvironment' : T_PrivateEnvironment_Record, # | T_Null
            'Realm'              : T_Realm_Record,
        }[component_name.source_text()]
        return (t, env0)

    elif p == r'{EXPR} : the byte elements of {var} concatenated and interpreted as a little-endian bit string encoding of an IEEE 754-2019 binary32 value':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_MathInteger_))
        return (T_IEEE_binary32_, env1)

    elif p == r'{EXPR} : the byte elements of {var} concatenated and interpreted as a little-endian bit string encoding of an IEEE 754-2019 binary64 value':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_MathInteger_))
        return (T_IEEE_binary64_, env1)

    elif p == r"{EXPR} : a copy of {var}'s _captures_ List":
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_State)
        return (T_captures_list_, env1)

    elif p in [
        r"{SETTABLE} : {var}[{EX}]",
        r"{SETTABLE} : {DOTTING}[{EX}]",
    ]:
        [seq_ex, subscript_var] = children
        (seq_type, seq_env) = tc_expr(seq_ex, env0); assert seq_env is env0
        env2 = env0.ensure_expr_is_of_type(subscript_var, T_MathInteger_); assert env2 is env0
        if isinstance(seq_type, ListType):
            item_type = seq_type.element_type
        elif seq_type == T_List:
            item_type = T_TBD
        elif seq_type.is_a_subtype_of_or_equal_to(T_Data_Block | T_Shared_Data_Block):
            item_type = T_MathInteger_
        elif seq_type.is_a_subtype_of_or_equal_to(T_Data_Block | T_Shared_Data_Block | T_Null):
            add_pass_error(
                expr,
                "STA fails to confirm that %s isnt Null" %
                (seq_ex.source_text())
            )
            item_type = T_MathInteger_
        else:
            assert 0, seq_type
        return (item_type, env0)

    elif p == r"{EXPR} : the State ({var}, {EX}, {var})":
        [input_var, ex, var] = children
        env0.assert_expr_is_of_type(input_var, ListType(T_character_))
        env1 = env0.ensure_expr_is_of_type(ex, T_MathInteger_); assert env1 is env0
        env2 = env0.ensure_expr_is_of_type(var, T_captures_list_); assert env2 is env0
        return (T_State, env0)

    elif p == r"{EXPR} : {var}'s State":
        # todo?: change to Assert: _r_ is a State
        [var] = children
        env0.assert_expr_is_of_type(var, T_State)
        return (T_State, env0)

    elif p == r"{EXPR} : an empty Set":
        [] = children
        return (T_Set, env0)

    elif p in [
        r"{EX} : &laquo; &raquo;",
    ]:
        [] = children
        return (T_List, env0)

    elif p in [
        r"{EX} : &laquo; {EXLIST} &raquo;",
    ]:
        [exlist] = children
        ex_types = set()
        for ex in exes_in_exlist(exlist):
            (ex_type, env1) = tc_expr(ex, env0); assert env1 is env0
            ex_types.add(ex_type)
        element_type = union_of_types(ex_types)
        list_type = ListType(element_type)
        return (list_type, env0)

    elif p == r"{EXPR} : {var}'s _captures_ List":
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_State)
        return (T_captures_list_, env1)

    elif p == r"{EX} : {DSBN}":
        [dsbn] = children
        return (T_SlotName_, env0)

    elif p in [
        r"{EXPR} : a newly created Property Descriptor with no fields",
        r"{EXPR} : a new Property Descriptor that initially has no fields",
    ]:
        [] = children
        return (T_Property_Descriptor, env0)

    elif p == r"{EXPR} : the fully populated data Property Descriptor for the property, containing the specified attributes for the property. For properties listed in {h_emu_xref}, {h_emu_xref}, or {h_emu_xref} the value of the {DSBN} attribute is the corresponding intrinsic object from {var}":
        [emu_xref1, emu_xref2, emu_xref3, dsbn, var] = children
        env0.assert_expr_is_of_type(var, T_Realm_Record)
        return (T_Property_Descriptor, env0)

    elif p == r"{EXPR} : {var}'s own property whose key is {var}":
        [obj_var, key_var] = children
        env0.assert_expr_is_of_type(obj_var, T_Object)
        env0.assert_expr_is_of_type(key_var, T_String | T_Symbol)
        return (T_property_, env0)

    elif p == r"{SETTABLE} : {var}'s {DSBN} attribute":
        [prop_var, dsbn] = children
        dsbn_name = dsbn.source_text()[2:-2]
        if dsbn_name in ['Enumerable', 'Configurable']:
            env0.assert_expr_is_of_type(prop_var, T_property_)
            result_type = T_Boolean
        elif dsbn_name in ['Value', 'Writable']:
            env0.assert_expr_is_of_type(prop_var, T_data_property_)
            result_type = T_Tangible_ if dsbn_name == 'Value' else T_Boolean
        elif dsbn_name in ['Get', 'Set']:
            env0.assert_expr_is_of_type(prop_var, T_accessor_property_)
            result_type = T_Object | T_Undefined
        else:
            assert 0
        return (result_type, env0)

    elif p == r"{SETTABLE} : the {DSBN} internal slot of this Date object":
        [dsbn] = children
        dsbn_name = dsbn.source_text()[2:-2]
        assert dsbn_name == 'DateValue'
        return (T_Number, env0)

    elif p == r"{EX} : a newly created {ERROR_TYPE} object":
        [error_type] = children
        return (type_for_ERROR_TYPE(error_type), env0)

    elif p in [
        r"{EXPR} : a copy of {var}",
    ]:
        [var] = children
        (t, env1) = tc_expr(var, env0); assert env1 is env0
        return (t, env1)

    elif p in [
        r"{EXPR} : a copy of the List {var}",
        r"{EXPR} : a List whose elements are the elements of {var}",
    ]:
        [var] = children
        t = env0.assert_expr_is_of_type(var, T_List)
        return (t, env0)

    elif p in [
        r"{EXPR} : the first element of {var}",
        r"{EXPR} : the second element of {var}",
        r"{EXPR} : the last element in {var}",
    ]:
        # todo: replace with ad hoc record
        [var] = children
        list_type = env0.assert_expr_is_of_type(var, T_List)
        return (list_type.element_type, env0)

    elif p in [
        r"{EXPR} : the sole element of {PP_NAMED_OPERATION_INVOCATION}",
        r"{EXPR} : the sole element of {var}",
    ]:
        [noi] = children
        list_type = env0.assert_expr_is_of_type(noi, T_List)
        return (list_type.element_type, env0)

    elif p in [
        r"{EXPR} : the element in {EX} whose {DSBN} is {EX}",
        r"{EXPR} : the element of {EX} whose {DSBN} field is {var}",
        r"{EXPR} : the element of {EX} whose {DSBN} is the same as {EX}",
    ]:
        [list_ex, dsbn, val_ex] = children
        dsbn_name = dsbn.source_text()[2:-2]
        (list_type, env1) = tc_expr(list_ex, env0); assert env1 is env0
        assert isinstance(list_type, ListType)
        et = list_type.element_type
        assert isinstance(et, NamedType)
        fields = fields_for_record_type_named_[et.name]
        whose_type = fields[dsbn_name]
        env1.assert_expr_is_of_type(val_ex, whose_type)
        return (et, env1)

    elif p == r"{EXPR} : a new Record":
        # Once, in CreateIntrinsics
        [] = children
        return (T_Intrinsics_Record, env0)

    elif p == r"{EXPR} : such an object created in a host-defined manner":
        [] = children
        return (T_Object, env0)

    elif p == r"{EXPR} : the canonical {h_emu_not_ref_property_name} of {var} as given in the &ldquo;Canonical {h_emu_not_ref_property_name}&rdquo; column of the corresponding row":
        [_, v, _] = children
        env0.assert_expr_is_of_type(v, ListType(T_code_point_))
        return (ListType(T_code_point_), env0)

    elif p == r"{EXPR} : the List of Unicode code points {var}":
        [v] = children
        env0.assert_expr_is_of_type(v, ListType(T_code_point_))
        return (ListType(T_code_point_), env0)

    elif p == r"{EXPR} : the canonical property value of {var} as given in the &ldquo;Canonical property value&rdquo; column of the corresponding row":
        [v] = children
        env0.assert_expr_is_of_type(v, ListType(T_code_point_))
        return (ListType(T_code_point_), env0)

    # ----

    elif p == r"{EXPR} : the WaiterList that is referenced by the pair ({var}, {var})":
        [sdb, i] = children
        env0.assert_expr_is_of_type(sdb, T_Shared_Data_Block)
        env0.assert_expr_is_of_type(i, T_MathInteger_)
        return (T_WaiterList, env0)

    elif p == r"{EXPR} : a reference to the list of waiters in {var}":
        [wl] = children
        env0.assert_expr_is_of_type(wl, T_WaiterList)
        return (ListType(T_agent_signifier_), env0)

    elif p == r"{EXPR} : the first waiter in {var}":
        [wl] = children
        env0.assert_expr_is_of_type(wl, ListType(T_agent_signifier_))
        return (T_agent_signifier_, env0)

    elif p in [
        r"{EX} : *this* value",
        r"{EX} : the *this* value",
    ]:
        return (T_Tangible_, env0)

    elif p == r"{EXPR} : the String value that is the result of normalizing {var} into the normalization form named by {var} as specified in {h_a}":
        [s_var, nf_var, h_a] = children
        env0.assert_expr_is_of_type(s_var, T_String)
        env0.assert_expr_is_of_type(nf_var, T_String)
        return (T_String, env0)

    elif p in [
        r"{EXPR} : the String value that is a copy of {var} with both leading and trailing white space removed",
        r"{EXPR} : the String value that is a copy of {var} with leading white space removed",
        r"{EXPR} : the String value that is a copy of {var} with trailing white space removed",
    ]:
        [var] = children
        env0.assert_expr_is_of_type(var, T_String)
        return (T_String, env0)

    elif p == r"{EXPR} : the String value containing the single code unit {var}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_code_unit_)
        return (T_String, env0)

    elif p == r"{EXPR} : the longest prefix of {var}, which might be {var} itself, that satisfies the syntax of a {nonterminal}":
        [var1, var2, nont] = children
        assert same_source_text(var1, var2)
        env0.assert_expr_is_of_type(var1, T_String)
        return (T_String, env0)

    elif p == r"{EXPR} : this Date object":
        [] = children
        return (T_Object | ThrowType(T_TypeError), env0)

    elif p == r"{EXPR} : the List that is {DOTTING}":
        [dotting] = children
        (dotting_type, env1) = tc_expr(dotting, env0); assert env1 is env0
        dotting_type.is_a_subtype_of_or_equal_to(T_List)
        return (dotting_type, env0)

    elif p == r"{EXPR} : the number of leading 1 bits in {var}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_MathNonNegativeInteger_)
        return (T_MathNonNegativeInteger_, env0)

    elif p == r"{EXPR} : the number of leading zero bits in the unsigned 32-bit binary representation of {var}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_IntegralNumber_)
        return (T_MathNonNegativeInteger_, env0)

    elif p == r"{EX} : the digits of the decimal representation of {var} (in order, with no leading zeroes)":
        [var] = children
        env0.assert_expr_is_of_type(var, T_MathInteger_)
        return (ListType(T_code_unit_), env0)

    elif p in [
        r"{EX} : the remaining {EX} code units of {var}",
        r"{EXPR} : the other {EX} code units of {var}",
    ]:
        [ex, var] = children
        env0.assert_expr_is_of_type(var, T_String)
        env1 = env0.ensure_expr_is_of_type(ex, T_MathInteger_)
        return (T_String, env1)

    elif p == r"{EX} : the first {SUM} code units of {var}":
        [summ, var] = children
        env0.assert_expr_is_of_type(var, T_String)
        env1 = env0.ensure_expr_is_of_type(summ, T_MathInteger_)
        return (T_String, env1)

    elif p == r"{EXPR} : the String value whose code units are the elements in the List {var}. If {var} has no elements, the empty String is returned":
        [list_var, list_var2] = children
        assert same_source_text(list_var, list_var2)
        env0.assert_expr_is_of_type(list_var, ListType(T_code_unit_))
        return (T_String, env0)

    elif p == r"{EXPR} : the String value that is made from {var} copies of {var} appended together":
        [n_var, s_var] = children
        env0.assert_expr_is_of_type(s_var, T_String)
        env1 = env0.ensure_expr_is_of_type(n_var, T_MathInteger_)
        return (T_String, env1)

    elif p in [
        r"{EX} : the GlobalSymbolRegistry List",
        r"{EX} : the GlobalSymbolRegistry List (see {h_emu_xref})",
    ]:
        return (ListType(T_GlobalSymbolRegistry_Record), env0)

    elif p == r"{EXPR} : a new unique Symbol value whose {DSBN} value is {var}":
        [dsbn, var] = children
        assert dsbn.source_text() == '[[Description]]'
        env0.assert_expr_is_of_type(var, T_String | T_Undefined)
        return (T_Symbol, env0)

    elif p == r"{EXPR} : the integer value that is represented by {var} in radix-{var} notation, using the letters <b>A</b>-<b>Z</b> and <b>a</b>-<b>z</b> for digits with values 10 through 35":
        [zvar, rvar] = children
        env0.assert_expr_is_of_type(zvar, T_String)
        env0.assert_expr_is_of_type(rvar, T_MathInteger_)
        return (T_MathInteger_, env0)

    elif p == r"{EXPR} : the String value consisting of repeated concatenations of {EX} truncated to length {var}":
        [ex, var] = children
        env0.assert_expr_is_of_type(ex, T_String)
        env1 = env0.ensure_expr_is_of_type(var, T_MathInteger_)
        return (T_String, env1)

    elif p == r"{EXPR} : the first agent in {var}":
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_agent_signifier_))
        return (T_agent_signifier_, env1)

    elif p == r"{EX} : {backticked_word}":
        [backticked_word] = children
        word = backticked_word.source_text()[1:-1]
        if word == 'General_Category':
            return (T_Unicode_code_points_, env0)
        else:
            assert 0, word

    elif p in [
        r"{EX} : the number of elements of {var}",
        r"{EX} : The number of elements in {var}",
    ]:
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_List)
        return (T_MathNonNegativeInteger_, env1)

    elif p == r"{EXPR} : the Record { {DSBN}, {DSBN} } that is the value of {EX}":
        [dsbna, dsbnb, ex] = children
        assert dsbna.source_text() == '[[Key]]'
        assert dsbnb.source_text() == '[[Value]]'
        env0.assert_expr_is_of_type(ex, T_MapData_record_)
        return (T_MapData_record_, env0)

    elif p == r"{EXPR} : the intrinsic function {percent_word}":
        [percent_word] = children
        return (T_function_object_, env0)

    elif p == r"{EXPR} : the implementation-defined list-separator String value appropriate for the host environment's current locale (such as {STR_LITERAL})":
        [str_lit] = children
        return (T_String, env0)

    elif p == r"{EXPR} : the index within {var} of the first such code unit":
        [var] = children
        env0.assert_expr_is_of_type(var, T_String)
        return (T_MathNonNegativeInteger_, env0)

    elif p == r"{EXPR} : the intrinsic object listed in column one of {h_emu_xref} for {DOTTING}":
        [emu_xref, dotting] = children
        env0.assert_expr_is_of_type(dotting, T_String)
        return (T_function_object_, env0)

    elif p == r"{EXPR} : the String value containing {var} occurrences of {code_unit_lit}":
        [n, lit] = children
        env0.assert_expr_is_of_type(lit, T_code_unit_)
        return (T_String, env0)

    elif p == '''{EXPR} : a String in the form of a {nonterminal} ({nonterminal} if {var} contains *"u"*) equivalent to {var} interpreted as UTF-16 encoded Unicode code points ({h_emu_xref}), in which certain code points are escaped as described below. {var} may or may not be identical to {var}; however, the Abstract Closure that would result from evaluating {var} as a {nonterminal} ({nonterminal} if {var} contains *"u"*) must behave identically to the Abstract Closure given by the constructed object's {DSBN} internal slot. Multiple calls to this abstract operation using the same values for {var} and {var} must produce identical results''':
        # XXX
        return (T_String, env0)

    elif p == r"{EX} : NewTarget":
        [] = children
        return (T_constructor_object_ | T_Undefined, env0)

    elif p == r"{EXPR} : the active function object":
        [] = children
        return (T_function_object_, env0)

    elif p == "{EX} : {h_code_quote}":
        [h_code_quote] = children
        return (T_String, env0)

    elif p == r"{EXPR} : the {var} that was passed to this function by {DSBN} or {DSBN}":
        [var, dsbna, dsbnb] = children
        assert var.source_text() == '_argumentsList_'
        # It's not a reference to an in-scope variable,
        # it's a reference to a variable at a higher level.
        # It's more of a reminder of where the '_args_' parameter comes from.
        return (ListType(T_Tangible_), env0)

    elif p == r"{EXPR} : the time value (UTC) identifying the current time":
        [] = children
        return (T_Number, env0)

    elif p == r"{EXPR} : the result of parsing {var} as a date, in exactly the same manner as for the `parse` method ({h_emu_xref})":
        [var, emu_xref] = children
        env0.assert_expr_is_of_type(var, T_String)
        return (T_Number, env0)

    elif p == r"{EXPR} : the String value of the Constructor Name value specified in {h_emu_xref} for this <var>TypedArray</var> constructor":
        [emu_xref] = children
        return (T_String, env0)

    elif p == r"{EXPR} : the Agent Events Record in {DOTTING} whose {DSBN} is {PP_NAMED_OPERATION_INVOCATION}":
        [dotting, dsbn, e] = children
        env0.assert_expr_is_of_type(dotting, ListType(T_Agent_Events_Record))
        assert dsbn.source_text() == '[[AgentSignifier]]'
        env0.assert_expr_is_of_type(e, T_agent_signifier_)
        return (T_Agent_Events_Record, env0)

    elif p in [
        r"{EXPR} : the result of converting {var} to a value in IEEE 754-2019 binary32 format using roundTiesToEven mode",
        r"{EXPR} : the result of converting {var} to a value in IEEE 754-2019 binary64 format",
        r"{EXPR} : the ECMAScript Number value corresponding to {var}",
    ]:
        [var] = children
        env0.assert_expr_is_of_type(var, T_Number)
        # XXX The intermediates are not really T_Number
        return (T_Number, env0)

    elif p == r"{EX} : The remainder of dividing {EX} by {EX}":
        [a, b] = children
        env0.assert_expr_is_of_type(a, T_MathInteger_)
        env0.assert_expr_is_of_type(b, T_MathInteger_)
        return (T_MathInteger_, env0)

    elif p == r"{PAIR} : ({EX}, {EX})":
        [a, b] = children
        # over-specific:
        env0.assert_expr_is_of_type(a, T_event_)
        env0.assert_expr_is_of_type(b, T_event_)
        return (T_event_pair_, env0)

    elif p == "{EXPR} : an implementation-defined String source code representation of {var}. The representation must have the syntax of a {nonterminal}. Additionally, if {var} has an {DSBN} internal slot and {DOTTING} is a String, the portion of the returned String that would be matched by {nonterminal} {nonterminal} must be the value of {DOTTING}":
        var = children[0]
        env0.assert_expr_is_of_type(var, T_function_object_)
        return (T_String, env0)

    elif p == r"{EXPR} : an implementation-defined String source code representation of {var}. The representation must have the syntax of a {nonterminal}":
        [var, nont] = children
        env0.assert_expr_is_of_type(var, T_function_object_)
        return (T_String, env0)

    # explicit-exotics:
    elif p in [
        r"{EX} : the internal slots listed in {h_emu_xref}",
    ]:
        # XXX really, the *names* of the internal slots...
        return (ListType(T_SlotName_), env0)

    elif p == r"{EX} : {backticked_oth}":
        [_] = children
        return (T_Unicode_code_points_, env0)

    elif p == r"{EXPR} : the value that {var} corresponds to in {h_emu_xref}":
        [var, xref] = children
        env1 = env0.ensure_expr_is_of_type(var, T_Primitive)
        assert xref.source_text() == '<emu-xref href="#table-tobigint"></emu-xref>'
        return (T_BigInt | ThrowType(T_TypeError) | ThrowType(T_SyntaxError), env1)

    elif p == r"{EX} : the Range {PAIR}":
        [pair] = children
        # XXX
        return (T_Range, env0)

    elif p == r"{EXPR} : a new Synchronize event":
        [] = children
        return (T_Synchronize_event, env0)

    elif p == r"{SETTABLE} : the Synchronize event in {var}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_WaiterList)
        return (T_Synchronize_event, env0)

    elif p == r"{EXPR} : the result of interpreting each of {var}'s 16-bit elements as a Unicode BMP code point. UTF-16 decoding is not applied to the elements":
        [var] = children
        env0.assert_expr_is_of_type(var, T_String)
        return (T_Unicode_code_points_, env0)

    # for PR #1961 compound_assignment
    elif p == r"{MULTILINE_EXPR} : the {TABLE_RESULT_TYPE} associated with {var} in the following table:{_indent_}{nlai}{h_figure}{_outdent_}":
        [table_result_type, var, h_figure] = children
        table_result_type_str = table_result_type.source_text()
        if table_result_type_str == 'sequence of Unicode code points':
            result_type = T_Unicode_code_points_
        else:
            assert 0, table_result_type_str
        return (result_type, env0)

    elif p == r"{MULTILINE_EXPR} : the {TABLE_RESULT_TYPE} associated with {var} and Type({var}) in the following table:{_indent_}{nlai}{h_figure}{_outdent_}":
        [table_result_type, vara, varb, h_figure] = children
        table_result_type_str = table_result_type.source_text()
        if table_result_type_str == 'abstract operation':
            # result_type = (
            #     ProcType([T_Number, T_Number], T_Number | T_throw_)
            #     |
            #     ProcType([T_BigInt, T_BigInt], T_BigInt | T_throw_)
            # )
            result_type = ProcType([T_Number|T_BigInt, T_Number|T_BigInt], T_Number|T_BigInt | T_throw_)
        else:
            assert 0, table_result_type_str
        return (result_type, env0)

    elif p == r"{EXPR} : an implementation-approximated Number value representing {EXPR}":
        [ex] = children
        env0.assert_expr_is_of_type(ex, T_MathReal_)
        return (T_Number, env0)

    elif p == r"{EX} : a nondeterministically chosen byte value":
        [] = children
        return (T_MathNonNegativeInteger_, env0)

    elif p == r"{EXPR} : the result of clamping {var} between 0 and {EX}":
        [var, upper_ex] = children
        env0.assert_expr_is_of_type(upper_ex, T_MathInteger_)
        env0.assert_expr_is_of_type(var, T_MathInteger_ | T_MathPosInfinity_ | T_MathNegInfinity_)
        return (T_MathNonNegativeInteger_, env0)

    elif p == r"{EXPR} : a List of one or more {ERROR_TYPE} objects representing the parsing errors and/or early errors. If more than one parsing error or early error is present, the number and ordering of error objects in the list is implementation-defined, but at least one must be present":
        [error_type] = children
        return (ListType(type_for_ERROR_TYPE(error_type)), env0)

    elif p == r"{EXPR} : that PrivateElement":
        [] = children
        return (T_PrivateElement, env0)

    elif p == r"{EXPR} : that Private Name":
        [] = children
        return (T_Private_Name, env0)

    elif p == r"{EXPR} : a new Private Name whose {dsb_word} value is {var}":
        [dsb_word, var] = children
        assert dsb_word.source_text() == '[[Description]]'
        env0.assert_expr_is_of_type(var, T_String)
        return (T_Private_Name, env0)

    elif p == r"{EXPR} : the Private Name in {var} whose {dsb_word} is {var}":
        [list_var, dsb_word, var] = children
        env0.assert_expr_is_of_type(list_var, ListType(T_Private_Name))
        assert dsb_word.source_text() == '[[Description]]'
        env0.assert_expr_is_of_type(var, T_String)
        return (T_Private_Name, env0)

    elif p == r"{EXPR} : the empty sequence of Unicode code points":
        [] = children
        return (T_Unicode_code_points_, env0)

    elif p == r"{EXPR} : a new {cap_word} object whose {dsb_word} internal slot is set to {var}. See {h_emu_xref} for a description of {cap_word} objects":
        [cap_word, dsb_word, var, emu_xref, cap_word2] = children
        T = cap_word.source_text()
        assert T in ['Boolean', 'Number', 'String', 'Symbol', 'BigInt']
        assert dsb_word.source_text() == f"[[{T}Data]]"
        assert var.source_text() == '_argument_'
        assert cap_word2.source_text() == T
        return (T_Object, env0)

    elif p in [
        r"{EXPR} : the mathematical value denoted by the result of replacing each significant digit in the decimal representation of {var} after the 20th with a 0 digit",
        r"{EXPR} : the mathematical value denoted by the result of replacing each significant digit in the decimal representation of {var} after the 20th with a 0 digit and then incrementing it at the 20th position (with carrying as necessary)",
    ]:
        [var] = children
        env0.assert_expr_is_of_type(var, T_MathReal_)
        return (T_MathReal_, env0)

    elif p == r"{EXPR} : an implementation-defined choice of either {var} or {var}":
        [vara, varb] = children
        env0.assert_expr_is_of_type(vara, T_MathReal_)
        env0.assert_expr_is_of_type(varb, T_MathReal_)
        return (T_MathReal_, env0)

    elif p == r"{EXPR} : a List whose elements are the elements of {var}, in the order in which they had their {dsb_word} fields set to {LITERAL} in {cap_word}":
        [var, dsb_word, literal, cap_word] = children
        assert dsb_word.source_text() == '[[AsyncEvaluation]]'
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_Cyclic_Module_Record))
        return (ListType(T_Cyclic_Module_Record), env1)

    elif p == r"{RHSS} : {RHSS}{RHS}":
        [rhss, rhs] = children
        (t1, env1) = tc_expr(rhss, env0)
        (t2, env2) = tc_expr(rhs, env1)
        return (t1 | t2, env2)

    elif p == r"{RHS} : {nlai}= {EXPR} if {CONDITION}":
        [expr, cond] = children
        (t_env, f_env) = tc_cond(cond, env0)
        (t, env1) = tc_expr(expr, t_env)
        return (t, env1)

    elif p == r"{EXPR} : a new implementation-defined Completion Record":
        [] = children
        return (T_Abrupt | T_Normal, env0)

    else:
        stderr()
        stderr("tc_expr:")
        stderr('    elif p == %s:' % escape(p))
        # pdb.set_trace()
        sys.exit(0)

# ------------------------------------------------------------------------------

def escape(s):
    if '"' in s:
        return '"' + s.replace('"', r'\"') + '"'
    else:
        return 'r"' + s + '"'

def same_source_text(a, b):
    return (a.source_text() == b.source_text())

# ------------------------------------------------------------------------------

def exes_in_exlist_opt(exlist_opt):
    assert exlist_opt.prod.lhs_s == '{EXLIST_OPT}'
    if exlist_opt.prod.rhs_s == '{EPSILON}':
        return []
    elif exlist_opt.prod.rhs_s == '{EXLIST}':
        [exlist] = exlist_opt.children
        return exes_in_exlist(exlist)
    else:
        assert 0, exlist_opt.prod.rhs_s

def exes_in_exlist(exlist):
    exes = []
    while True:
        assert exlist.prod.lhs_s == '{EXLIST}'
        if exlist.prod.rhs_s == '{EX}':
            [ex] = exlist.children
            exes.insert(0, ex)
            break
        elif exlist.prod.rhs_s == '{EXLIST}, {EX}':
            [inner_exlist, ex] = exlist.children
            exes.insert(0, ex)
            exlist = inner_exlist
        else:
            assert 0
    return exes

def tc_ao_invocation(callee_op_name, args, expr, env0):
    callee_op = spec.alg_info_['op'][callee_op_name]
    assert callee_op.species == 'op: singular'
    params = callee_op.parameters_with_types
    env1 = tc_args(params, args, env0, expr)
    return_type = callee_op.return_type
    return (return_type, env1)

def tc_sdo_invocation(op_name, main_arg, other_args, context, env0):
    op = spec.alg_info_['op'][op_name]
    assert op.species == 'op: discriminated by syntax: steps'

    env1 = env0.ensure_expr_is_of_type(main_arg, T_Parse_Node)
    # XXX expectation should be specific to what the callee accepts

    env2 = tc_args(op.parameters_with_types, other_args, env1, context)

    # seed:
    # if op_name == 'Evaluation': return (T_Tangible_, env0)
    # 'Contains': T_Boolean

    rt = op.return_type

    if op_name == 'Evaluation':
        # In some (most?) cases, evaluation can't return the full gamut of abrupt completions.
        # So sometimes, we can provide a narrower return type.
        assert T_Abrupt.is_a_subtype_of_or_equal_to(rt)
        mast = main_arg.source_text()

        if mast in [
            '|FunctionStatementList|',
        ]:
            # Might return a throw|return completion, but not continue|break
            (_, narrowed_rt) = rt.split_by(T_continue_ | T_break_)
            rt = narrowed_rt

        elif mast in [
            '_scriptBody_',
            '_body_', # |ScriptBody|
            '_lhs_',
            '_module_.[[ECMAScriptCode]]',
            '|DestructuringAssignmentTarget|',
            '|PropertyName|',
        ]:
            # Might return a throw completion, but not return|continue|break
            (_, narrowed_rt) = rt.split_by(T_continue_ | T_break_ | T_return_)
            rt = narrowed_rt

    return (rt, env2)

def with_fake_param_names(param_types):
    return [
        ('$%d' % (i+1), t )
        for (i, t) in enumerate(param_types)
    ]

def type_corresponding_to_comptype_literal(comptype_literal):
    assert isinstance(comptype_literal, ANode)
    return {
        '~normal~'  : T_Normal,
        '~continue~': T_continue_,
        '~break~'   : T_break_,
        '~return~'  : T_return_,
        '~throw~'   : T_throw_,
    }[comptype_literal.source_text()]

def tc_args( params, args, env0, context ):
    assert len(args) <= len(params)
    out_env = env0
    for ((param_name, param_type), arg) in zip_longest(params, args):

        if param_type == T_TBD:
            # Not much useful checking we can do.
            passed_part_of_param_type     = T_TBD
            not_passed_part_of_param_type = T_TBD
        else:
            (not_passed_part_of_param_type, passed_part_of_param_type) = param_type.split_by(T_not_passed)

        if arg is None:
            # No arg was passed to this parameter.
            if not_passed_part_of_param_type != T_0:
                # but the parameter is optional, so that's okay.
                pass
            else:
                # the parameter is not optional!
                add_pass_error(
                    context,
                    "No arg passed to non-optional param '%s'" % param_name
                )
        else:
            (arg_type, env1) = tc_expr(arg, env0)

            pt = passed_part_of_param_type

            env2 = env1 # overwritten in one case below:

            # Treat T_TBD like Top
            if pt == T_TBD:
                # This should only happen if the called operation
                # is in the same cluster as the calling operation.
                # (In particular, if the operation is calling itself.)
                #
                # Conceivably, we could go to the called operation and tell it
                # that this parameter must be able to accept arg_type.
                # However, let's assume that the current mechanisms will take care of it.
                # That is, by the end of this pass (on this cluster),
                # that pt will be refined,
                # and, in a subsequent pass, we'll be checking against that refined type.
                pass
            elif arg_type == T_TBD:
                env2 = env1.ensure_expr_is_of_type(arg, pt)
            elif arg_type.is_a_subtype_of_or_equal_to(pt):
                # normal case
                pass
            elif arg_type == T_List and isinstance(pt, ListType):
                # XXX: Still need this?
                # This happens when the arg is an List constructor with no items.
                # Not really worth complaining about.
                pass
            else:
                if (
                    # This condition, by focusing on T_throw_, is over-specific,
                    # but I'm guessing it catches the common cases.
                    T_throw_.is_a_subtype_of_or_equal_to(arg_type)
                    and
                    not T_throw_.is_a_subtype_of_or_equal_to(pt)
                ):
                    extra_msg = f' (arg could be abrupt completion?)'
                else:
                    extra_msg = ''

                add_pass_error(
                    arg,
                    "arg %s has type %s, but param %s requires type %s%s"
                    % (arg.source_text(), arg_type, param_name, pt, extra_msg)
                )
                # The parameter-type might be too narrow,
                # or the arg-type might be too wide.
                # We don't know which is the problem.
                # So we just note the mismatch and go on. Hm.

            out_env = env_and(out_env, env2)

    return out_env

# ------------------------------------------------------------------------------

def is_simple_call(ex):
    prefix_paren = ex.is_a('{PREFIX_PAREN}')
    if prefix_paren is None: return None
    if prefix_paren.prod.rhs_s != '{OPN_BEFORE_PAREN}({EXLIST_OPT})': return None
    [opn, exlist_opt] = prefix_paren.children

    if opn.prod.rhs_s in ['{DOTTING}', '{var}', '{var}.{cap_word}']: return None
    op_name = opn.source_text()

    var = exlist_opt.is_a('{var}')
    if var is None: return None

    return (op_name, var)

# ------------------------------------------------------------------------------

def get_field_names(fields):
    return [
        dsbn_name
        for (dsbn_name, ex) in get_field_items(fields)
    ]

def get_field_items(fields):
    for field in get_fields(fields):
        assert str(field.prod) == '{FIELD} : {DSBN}: {EX}'
        [dsbn, ex] = field.children
        dsbn_name = dsbn.source_text()[2:-2]
        yield (dsbn_name, ex)

def get_fields(fields):
    assert fields.prod.lhs_s == '{FIELDS}'
    if fields.prod.rhs_s == '{FIELDS}, {FIELD}':
        [prefields, field] = fields.children
        return get_fields(prefields) + [field]

    elif fields.prod.rhs_s == '{FIELD}':
        [field] = fields.children
        return [field]

    else:
        assert 0

# ------------------------------------------------------------------------------

fields_for_record_type_named_ = {

    # 6.2.4
    'Reference Record': {
        'Base'           : T_Tangible_ | T_Environment_Record | T_Unresolvable_,
        'ReferencedName' : T_String | T_Symbol | T_Private_Name,
        'Strict'         : T_Boolean,
        'ThisValue'      : T_Tangible_ | T_empty_,
    },

    # 6.2.5
    'Property Descriptor': { # XXX not modelling this very well
        # table 2
        'Value'       : T_Tangible_,
        'Writable'    : T_Boolean,
        # table 3
        'Get'         : T_Object | T_Undefined,
        'Set'         : T_Object | T_Undefined,
        # common
        'Enumerable'  : T_Boolean,
        'Configurable': T_Boolean,
    },

    #? # 2651: Table 8: Completion Record Fields
    #? 'Completion Record': {
    #?     'Type'   : T_completion_kind_,
    #?     'Value'  : T_Tangible_ | T_empty_,
    #?     'Target' : T_String | T_empty_,
    #? },

    # 6.2.9 The PrivateElement Specification Type
    'PrivateElement': {
        'Key'  : T_Private_Name,
        'Kind' : T_PrivateElementKind_,
        'Value': T_Tangible_,
        'Get'  : T_Undefined | T_function_object_,
        'Set'  : T_Undefined | T_function_object_,
    },
    # 6.2.10 The ClassFieldDefinition Record Specification Type
    'ClassFieldDefinition Record' : {
        'Name'                          : T_Private_Name | T_String | T_Symbol,
        'Initializer'                   : T_function_object_ | T_empty_,
        'IsAnonymousFunctionDefinition' : T_Boolean,
    },

    'ClassStaticBlockDefinition Record' : {
        'BodyFunction' : T_function_object_,
    },

    # 7.4.1 Iterator Records
    'Iterator Record': {
        'Iterator'  : T_Object, # iterator_object_ ?
        'NextMethod': T_function_object_,
        'Done'      : T_Boolean,
    },

    # 8.1
    'Environment Record': {
        'OuterEnv'         : T_Environment_Record,
    },

    'Declarative Environment Record': {
        'OuterEnv' : T_Environment_Record,
    },

    'Object Environment Record': {
        'OuterEnv'           : T_Environment_Record,
        'BindingObject'      : T_Object,
        'IsWithEnvironment'  : T_Boolean,
    },

    # 8.1.1.3 Table 16: Additional Fields of Function Environment Records
    'Function Environment Record': {
        'OuterEnv'         : T_Environment_Record,
        'ThisValue'        : T_Tangible_,
        'ThisBindingStatus': T_this_binding_status_, # T_String, # enumeration
        'FunctionObject'   : T_function_object_,
        'HomeObject'       : T_Object | T_Undefined,
        'NewTarget'        : T_Object | T_Undefined,
    },

    # 8.1.1.4 Table 18: Additional Fields of Global Environment Records
    'Global Environment Record': {
        'OuterEnv'         : T_Environment_Record,
        'ObjectRecord'     : T_Object_Environment_Record,
        'GlobalThisValue'  : T_Object,
        'DeclarativeRecord': T_Declarative_Environment_Record,
        'VarNames'         : ListType(T_String),
    },

    'Module Environment Record': {
        'OuterEnv'         : T_Environment_Record,
    },

    # 8.2 Realms: Table 21: Realm Record Fields
    'Realm Record': {
        'Intrinsics'  : T_Intrinsics_Record,
        'GlobalObject': T_Object,
        'GlobalEnv'   : T_Environment_Record,
        'TemplateMap' : ListType(T_templateMap_entry_),
        'HostDefined' : T_host_defined_ | T_Undefined,
    },

    # 8.2: NO TABLE
    'templateMap_entry_': {
        'Site'    : T_Parse_Node,
        'Array'   : T_Object,
    },

    # 8.4.1
    'JobCallback Record': {
        'Callback'    : T_function_object_,
        'HostDefined' : T_Top_,
    },

    # 8.6 Agents: Agent Record Fields
    'Agent Record': {
        'LittleEndian': T_Boolean,
        'CanBlock'    : T_Boolean,
        'Signifier'   : T_agent_signifier_,
        'IsLockFree1' : T_Boolean,
        'IsLockFree2' : T_Boolean,
        'IsLockFree8' : T_Boolean,
        'CandidateExecution': T_candidate_execution,
        'KeptAlive'   : ListType(T_Object),
    },

    # 9.2
    'PrivateEnvironment Record': {
        'OuterPrivateEnvironment': T_PrivateEnvironment_Record | T_Null,
        'Names'                  : ListType(T_Private_Name),
    },

    # 11933: NO TABLE, no mention
    'CodePointAt_record_': {
        'CodePoint'          : T_code_point_,
        'CodeUnitCount'      : T_MathInteger_,
        'IsUnpairedSurrogate': T_Boolean,
    },

    # PR 1892 (add import.meta):
    # 14234: no table
    'ImportMeta_record_': {
        'Key'   : T_String | T_Symbol,
        'Value' : T_Tangible_,
    },

    # 21275: NO TABLE, no mention
    'methodDef_record_': {
        'Closure' : T_function_object_,
        'Key'     : T_String | T_Symbol,
    },

    # 21832: Script Record Fields
    'Script Record': {
        'Realm'         : T_Realm_Record | T_Undefined,
        'ECMAScriptCode': T_PTN_Script,
        'HostDefined'   : T_host_defined_ | T_Undefined,
    },

    # 22437: Table 36: Module Record Fields
    'Module Record': {
        'Realm'           : T_Realm_Record | T_Undefined,
        'Environment'     : T_Environment_Record | T_empty_,
        'Namespace'       : T_Object | T_empty_,
        'HostDefined'     : T_host_defined_ | T_Undefined,
    },

    'other Module Record': {
        'Realm'           : T_Realm_Record | T_Undefined,
        'Environment'     : T_Environment_Record | T_empty_,
        'Namespace'       : T_Object | T_empty_,
        'HostDefined'     : T_host_defined_ | T_Undefined,
    },

    #
    'Cyclic Module Record': {
        'Realm'           : T_Realm_Record | T_Undefined,
        'Environment'     : T_Environment_Record | T_empty_,
        'Namespace'       : T_Object | T_empty_,
        'HostDefined'     : T_host_defined_ | T_Undefined,
        #
        'Status'          : T_module_record_status_, # T_String,
        'EvaluationError'  : T_throw_ | T_empty_,
        'DFSIndex'         : T_MathInteger_ | T_empty_,
        'DFSAncestorIndex' : T_MathInteger_ | T_empty_,
        'RequestedModules' : ListType(T_String),
        'CycleRoot'        : T_Cyclic_Module_Record | T_empty_,
        'HasTLA'           : T_Boolean,
        'AsyncEvaluation'  : T_Boolean,
        'TopLevelCapability': T_PromiseCapability_Record | T_empty_,
        'AsyncParentModules': ListType(T_Cyclic_Module_Record),
        'PendingAsyncDependencies': T_MathInteger_ | T_empty_,
    },

    # 23406: Table 38: Additional Fields of Source Text Module Records
    'Source Text Module Record': {
        'Realm'           : T_Realm_Record | T_Undefined,
        'Environment'     : T_Environment_Record | T_empty_,
        'Namespace'       : T_Object | T_empty_,
        'HostDefined'     : T_host_defined_ | T_Undefined,
        #
        'Status'          : T_module_record_status_, # T_String,
        'EvaluationError'  : T_throw_ | T_empty_,
        'DFSIndex'         : T_MathInteger_ | T_empty_,
        'DFSAncestorIndex' : T_MathInteger_ | T_empty_,
        'RequestedModules' : ListType(T_String),
        'CycleRoot'        : T_Cyclic_Module_Record | T_empty_,
        'HasTLA'           : T_Boolean,
        'AsyncEvaluation'  : T_Boolean,
        'TopLevelCapability': T_PromiseCapability_Record | T_empty_,
        'AsyncParentModules': ListType(T_Cyclic_Module_Record),
        'PendingAsyncDependencies': T_MathInteger_ | T_empty_,
        #
        'Context'              : T_execution_context | T_empty_,
        'ECMAScriptCode'       : T_Parse_Node,
        'Context'              : T_execution_context | T_empty_, # PR 1670
        'ImportMeta'           : T_Object | T_empty_, # PR 1892
        'ImportEntries'        : ListType(T_ImportEntry_Record),
        'LocalExportEntries'   : ListType(T_ExportEntry_Record),
        'IndirectExportEntries': ListType(T_ExportEntry_Record),
        'StarExportEntries'    : ListType(T_ExportEntry_Record),
    },

    # 23376
    'ResolvedBinding Record': {
        'Module'      : T_Module_Record,
        'BindingName' : T_String | T_TildeNamespace_,
    },

    # 23490: Table 39: ImportEntry Record Fields
    'ImportEntry Record': {
        'ModuleRequest': T_String,
        'ImportName'   : T_String | T_TildeNamespaceObject_,
        'LocalName'    : T_String,
    },

    # 23627: Table 41: ExportEntry Record Fields
    'ExportEntry Record': {
        'ExportName'    : T_String | T_Null,
        'ModuleRequest' : T_String | T_Null,
        'ImportName'    : T_String | T_Null | T_TildeAll_ | T_TildeAllButDefault_,
        'LocalName'     : T_String | T_Null,
    },

    # 24003
    'ExportResolveSet_Record_': {
        'Module'     : T_Module_Record,
        'ExportName' : T_String,
    },

    # 28088: table-44: GlobalSymbolRegistry Record Fields
    'GlobalSymbolRegistry Record': {
        'Key'   : T_String,
        'Symbol': T_Symbol,
    },

    # 22.2.2.?
    'QuantifierResultRecord_': {
        'Min'   : T_MathNonNegativeInteger_,
        'Max'   : T_MathNonNegativeInteger_ | T_MathPosInfinity_,
        'Greedy': T_Boolean,
    },
    'QuantifierPrefixResultRecord_': {
        'Min'   : T_MathNonNegativeInteger_,
        'Max'   : T_MathNonNegativeInteger_ | T_MathPosInfinity_,
    },
    'CharacterClassResultRecord_': {
        'CharSet': T_CharSet,
        'Invert' : T_Boolean,
    },

    'RegExp Record': {
        'IgnoreCase'    : T_Boolean,
        'Multiline'     : T_Boolean,
        'DotAll'        : T_Boolean,
        'Unicode'       : T_Boolean,
        'WordCharacters': T_CharSet,
        'CapturingGroupsCount': T_MathNonNegativeInteger_,
    },

    # 22.2.5.2.5 Match Record Fields
    'Match Record': {
        'StartIndex': T_MathInteger_,
        'EndIndex'  : T_MathInteger_,
    },

    # 38121 24.5.2: JSON.stringify: no table, no mention
    'JSON Serialization Record': {
        'ReplacerFunction': T_function_object_ | T_Undefined,
        'Stack'           : ListType(T_Object),
        'Indent'          : T_String,
        'Gap'             : T_String,
        'PropertyList'    : ListType(T_String) | T_Undefined,
    },

    # 25.2.3.2 FinalizationRegistry.prototype.register
    'FinalizationRegistryCellRecord_': {
        'WeakRefTarget'  : T_Object | T_empty_,
        'HeldValue'      : T_Tangible_,
        'UnregisterToken': T_Object | T_empty_,
    },

    # 26.6.1.1 PromiseCapability Record Fields
    'PromiseCapability Record': {
        'Promise' : T_Object | T_Undefined,
        'Resolve' : T_function_object_ | T_Undefined,
        'Reject'  : T_function_object_ | T_Undefined,
    },

    # 26.6.1.2 PromiseReaction Record Fields
    'PromiseReaction Record': {
        'Capability' : T_PromiseCapability_Record | T_Undefined,
        'Type'       : T_settlement_type_, # T_String,
        'Handler'    : T_JobCallback_Record | T_empty_,
    },

    # 39099: no table, no mention
    'MapData_record_': {
        'Key'   : T_Tangible_ | T_empty_,
        'Value' : T_Tangible_ | T_empty_,
        # but Value is empty only if Key is empty?
        # So if you establish that _e_.[[Key]] isn't ~empty~,
        # you know that _e_.[[Value]] isn't ~empty~ ?
    },

    # 39328: 28.2 Agent Events Record Fields
    'Agent Events Record' : {
        'AgentSignifier'       : T_agent_signifier_,
        'EventList'            : ListType(T_event_),
        'AgentSynchronizesWith': ListType(T_event_pair_),
    },

    # 39380: Candidate Execution Record Fields
    'candidate execution': {
        'EventsRecords'       : ListType(T_Agent_Events_Record),
        'ChosenValues'        : ListType(T_Chosen_Value_Record),
        'AgentOrder'          : T_Relation,
        'ReadsBytesFrom'      : ProcType([T_event_], ListType(T_WriteSharedMemory_event | T_ReadModifyWriteSharedMemory_event)),
        'ReadsFrom'           : T_Relation,
        'HostSynchronizesWith': T_Relation,
        'SynchronizesWith'    : T_Relation,
        'HappensBefore'       : T_Relation,
    },

    # 39415: CreateResolvingFunctions NO TABLE, not even mentioned
    # 29803: `Promise.all` Resolve Element Functions NO TABLE, barely mentioned
    'boolean_value_record_': {
        'Value' : T_Boolean,
    },

    # 39438: CreateResolvingFunctions NO TABLE, not even mentioned
    'ResolvingFunctions_record_': {
        'Resolve' : T_function_object_,
        'Reject'  : T_function_object_,
    },

    # 39769: NO TABLE, not even mentioned
    'Job_record_': {
        'Job'  : T_Job,
        'Realm': T_Realm_Record | T_Null,
    },

    # 39784: PerformPromiseAll NO TABLE, not even mentioned
    'integer_value_record_': {
        'Value' : T_MathInteger_,
    },

    # 40060 ...
    'Shared Data Block event': {
        'Order'       : T_SharedMemory_ordering_, # T_String,
        'NoTear'      : T_Boolean,
        'Block'       : T_Shared_Data_Block,
        'ByteIndex'   : T_MathInteger_,
        'ElementSize' : T_MathInteger_,
    },

    # repetitive, but easier than factoring out...
    'ReadSharedMemory event': {
        'Order'       : T_SharedMemory_ordering_, # T_String,
        'NoTear'      : T_Boolean,
        'Block'       : T_Shared_Data_Block,
        'ByteIndex'   : T_MathInteger_,
        'ElementSize' : T_MathInteger_,
    },

    'WriteSharedMemory event': {
        'Order'       : T_SharedMemory_ordering_, # T_String,
        'NoTear'      : T_Boolean,
        'Block'       : T_Shared_Data_Block,
        'ByteIndex'   : T_MathInteger_,
        'ElementSize' : T_MathInteger_,
        'Payload'     : ListType(T_MathInteger_),
    },

    'ReadModifyWriteSharedMemory event': {
        'Order'       : T_SharedMemory_ordering_, # T_String,
        'NoTear'      : T_Boolean,
        'Block'       : T_Shared_Data_Block,
        'ByteIndex'   : T_MathInteger_,
        'ElementSize' : T_MathInteger_,
        'Payload'     : ListType(T_MathInteger_),
        'ModifyOp'    : T_ReadModifyWrite_modification_closure,
    },

    # 40224: Chosen Value Record Fields
    'Chosen Value Record': {
        'Event'       : T_Shared_Data_Block_event,
        'ChosenValue' : ListType(T_MathInteger_),
    },
    # 41899: AsyncGeneratorRequest Record Fields
    'AsyncGeneratorRequest Record': {
        'Completion' : T_Tangible_ | T_empty_ | T_return_ | T_throw_,
        'Capability' : T_PromiseCapability_Record,
    },

}


type_of_internal_thing_ = {

    # Ordinary Object Internal Methods and Internal Slots
    'Prototype'  : T_Object | T_Null,
    'Extensible' : T_Boolean,

    'PrivateElements'   : ListType(T_PrivateElement),

    # 1188: Table 5: Essential Internal Methods
    # (Properly, this info *should* be taken from the results of STA.)
    'GetPrototypeOf'    : ProcType([                                             ], T_Object | T_Null                   | T_throw_),
    'SetPrototypeOf'    : ProcType([T_Object | T_Null                            ], T_Boolean                           | T_throw_),
    'IsExtensible'      : ProcType([                                             ], T_Boolean                           | T_throw_),
    'PreventExtensions' : ProcType([                                             ], T_Boolean                           | T_throw_),
    'GetOwnProperty'    : ProcType([T_String | T_Symbol                          ], T_Property_Descriptor | T_Undefined | T_throw_),
    'DefineOwnProperty' : ProcType([T_String | T_Symbol, T_Property_Descriptor   ], T_Boolean                           | T_throw_),
    'HasProperty'       : ProcType([T_String | T_Symbol                          ], T_Boolean                           | T_throw_),
    'Get'               : ProcType([T_String | T_Symbol, T_Tangible_             ], T_Tangible_                         | T_throw_),
    'Set'               : ProcType([T_String | T_Symbol, T_Tangible_, T_Tangible_], T_Boolean                           | T_throw_),
    'Delete'            : ProcType([T_String | T_Symbol                          ], T_Boolean                           | T_throw_),
    'OwnPropertyKeys'   : ProcType([                                             ], ListType(T_String | T_Symbol)       | T_throw_),

    # 1328: Table 6: Additional Essential Internal Methods of Function Objects
    'Call'              : ProcType([T_Tangible_, ListType(T_Tangible_)           ], T_Tangible_                         | T_throw_),
    'Construct'         : ProcType([ListType(T_Tangible_), T_Object              ], T_Object                            | T_throw_),

    # 4407
    'NumberData' : T_Number,
    # 4423
    'SymbolData' : T_Symbol,
    # 5994
    'BigIntData' : T_BigInt,

    # 5253: NO TABLE, no mention
    'IteratedList'          : ListType(T_Tangible_),
    'ListNextIndex'         : T_MathInteger_,

    # 8329: Table 30: Internal Slots of ECMAScript Function Objects
    'Environment'      : T_Environment_Record,
    'PrivateEnvironment' : T_PrivateEnvironment_Record | T_Null,
    'FormalParameters' : T_Parse_Node,
    'FunctionKind'     : T_FunctionKind2_, # T_String, # could be more specific
    'IsClassConstructor': T_Boolean, # PR 15xx re FunctionKind
    'ECMAScriptCode'   : T_Parse_Node,
    'ConstructorKind'  : T_constructor_kind_, # T_String, # could be more specific
    'Realm'            : T_Realm_Record,
    'ScriptOrModule'   : T_Script_Record | T_Module_Record | T_Null, # XXX must add Null to spec
    'ThisMode'         : T_this_mode,
    'Strict'           : T_Boolean,
    'HomeObject'       : T_Object,
    'SourceText'       : T_Unicode_code_points_,
    'Fields'           : ListType(T_ClassFieldDefinition_Record),
    'PrivateMethods'   : ListType(T_PrivateElement),
    'ClassFieldInitializerName': T_String | T_Symbol | T_Private_Name | T_empty_,

    # 8860:
    'InitialName' : T_Null | T_String,

    # 9078: Table 28: Internal Slots of Exotic Bound Function Objects
    'BoundTargetFunction': T_function_object_,
    'BoundThis'          : T_Tangible_,
    'BoundArguments'     : ListType(T_Tangible_),

    # 9373 NO TABLE
    'StringData' : T_String,

    # 9506: Arguments Exotic Objects NO TABLE
    'ParameterMap' : T_Object,

    # 9735: MakeArgGetter NO TABLE
    'Name' : T_String,
    'Env'  : T_Environment_Record,

    # 9806: Integer Indexed Exotic Objects NO TABLE
    'ViewedArrayBuffer' : T_ArrayBuffer_object_ | T_SharedArrayBuffer_object_, #?
    'ArrayLength'       : T_MathInteger_,
    'ByteOffset'        : T_MathInteger_,
    'ContentType'       : T_numeric_primitive_type_, # T_String,
    'TypedArrayName'    : T_String,

    # 10066: Table 29: Internal Slots of Module Namespace Exotic Objects
    'Module'     : T_Module_Record, # T_Cyclic_Module_Record ?
    'Exports'    : ListType(T_String),

    # 9.5 Proxy Object Internal Methods and Internal Slots
    'ProxyHandler' : T_Object | T_Null,
    'ProxyTarget'  : T_Object | T_Null,

    # 18100: Properties of For-In Iterator Instances
    'Object'          : T_Object,
    'ObjectWasVisited': T_Boolean,
    'VisitedKeys'     : ListType(T_String),
    'RemainingKeys'   : ListType(T_String),

    # 24411
    'ReferencingScriptOrModule': T_Script_Record | T_Module_Record | T_Null,
    'Specifier'                : T_String,
    'PromiseCapability'        : T_PromiseCapability_Record,

    # 27137: Properties of Boolean Instances NO TABLE
    'BooleanData' : T_Boolean,

    # 30688
    'DateValue': T_IntegralNumber_ | T_NaN_Number_,

    # 30738: Table 46: Internal Slots of String Iterator Instances
    'IteratedString' : T_String,
    'StringNextIndex': T_MathInteger_,

    # 32711: Properties of RegExp Instances NO TABLE
    'RegExpMatcher'  : T_RegExpMatcher_,
    'OriginalSource' : T_String,
    'OriginalFlags'  : T_String,
    'RegExpRecord'   : T_RegExp_Record,

    # 34123: Table 48: Internal Slots of Array Iterator Instances
    'IteratedArrayLike'      : T_Object,
    'ArrayLikeNextIndex'     : T_MathInteger_,
    'ArrayLikeIterationKind' : T_iteration_result_kind_, # T_String,

    # 35373 + 37350 NO TABLE
    'ByteLength' : T_MathInteger_,

    # 35719: Table 50: Internal Slots of Map Iterator Instances
    'IteratedMap'      : T_Object,
    'MapNextIndex'     : T_MathInteger_,
    'MapIterationKind' : T_iteration_result_kind_, # T_String,

    # 36073: Table 51: Internal Slots of Set Iterator Instances
    'IteratedSet'      : T_Object,
    'SetNextIndex'     : T_MathInteger_,
    'SetIterationKind' : T_iteration_result_kind_, # T_String,

    # 36630: Table 58: Internal Slots of RegExp String Iterator Instances
    'IteratingRegExp'  : T_Object,
    'IteratedString'   : T_String,
    'Global'           : T_Boolean,
    'Unicode'          : T_Boolean,
    'Done'             : T_Boolean,

    # 36817: Properties of the ArrayBuffer Instances
    # 36973: Properties of the SharedArrayBuffer Instances
    # NO TABLE
    'ArrayBufferData': T_Data_Block | T_Shared_Data_Block | T_Null,
        # XXX but IsSharedArrayBuffer() ensures that ArrayBufferData is a Shared Data Block
    'ArrayBufferByteLength' : T_MathInteger_,
    'ArrayBufferDetachKey'  : T_host_defined_,

    # 38581: Table 56: Internal Slots of Generator Instances
    'GeneratorState'  : T_Undefined | T_generator_state_, # T_String,
    'GeneratorContext': T_execution_context,
    'GeneratorBrand'  : T_String | T_empty_,

    # 25.1.1.1 WeakRef ( _target_ ) NO TABLE
    'WeakRefTarget' : T_Object,

    # 25.2.1.1 FinalizationRegistry ( cleanupCallback ) NO TABLE
    'CleanupCallback' : T_JobCallback_Record,
    'Cells'           : ListType(T_FinalizationRegistryCellRecord_),

    # 38914: 25.4.1.3.1 ish, NO TABLE
    'Promise'        : T_Object,
    'AlreadyResolved': T_boolean_value_record_,

    # 39021
    'MapData' : ListType(T_MapData_record_),

    # 39034: NO TABLE
    'Capability' : T_PromiseCapability_Record,

    # 39537: Table 59: Internal Slots of Promise Instances
    'PromiseState'           : T_promise_state_, # T_String,
    'PromiseResult'          : T_Tangible_,
    'PromiseFulfillReactions': ListType(T_PromiseReaction_Record) | T_Undefined,
    'PromiseRejectReactions' : ListType(T_PromiseReaction_Record) | T_Undefined,
    'PromiseIsHandled'       : T_Boolean,

    # 39763
    'SetData'    : ListType(T_Tangible_ | T_empty_),

    # 39781 AsyncFunction Awaited Fulfilled/Rejected NO TABLE
    'AsyncContext' : T_execution_context,

    # 39817 `Promise.all` Resolve Element Functions
    'Index'             : T_MathInteger_,
    'Values'            : ListType(T_Tangible_),
    'Capability'        : T_PromiseCapability_Record,
    'RemainingElements' : T_integer_value_record_,
    'AlreadyCalled'     : T_boolean_value_record_ | T_Boolean,

    # 40093:
    'WeakMapData' : ListType(T_MapData_record_),

    # 40188: NO TABLE
    'Done'              : T_Boolean,

    # 40254:
    'WeakSetData' : ListType(T_Tangible_ | T_empty_),

    # 40578: NO TABLE
    'Errors' : ListType(T_Tangible_),

    # 41310: Table N: Internal Slots of Async-from-Sync Iterator Instances
    'SyncIteratorRecord' : T_Iterator_Record,

    # 41869: Table N: Internal Slots of AsyncGenerator Instances
    'AsyncGeneratorState'   : T_Undefined | T_generator_state_, # T_String,
    'AsyncGeneratorContext' : T_execution_context,
    'AsyncGeneratorQueue'   : ListType(T_AsyncGeneratorRequest_Record),

    # 42071 mention, NO TABLE
    'Generator' : T_AsyncGenerator_object_,

    # 44654 mention
    'Constructor' : T_constructor_object_,
    'OnFinally'   : T_function_object_,

    # 45286 mention
    'RevocableProxy' : T_Proxy_exotic_object_ | T_Null,
}

main()

# vim: sw=4 ts=4 expandtab
