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
from DecoratedFuncDict import DecoratedFuncDict

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

    shared.prep_for_line_info()

    for bif_or_op in ['bif', 'op']:
        for alg in spec.alg_info_[bif_or_op].values():
            # Ignore most headers in Annex B
            alg.headers = [
                header
                for header in alg.headers
                if retain_for_sta(header)
            ]
            for header in alg.headers:
                header.tah = TypedAlgHeader(header)

    print_unused_type_tweaks()

    process_declared_record_type_info()

    set_up_declared_internal_methods_and_slots()

def retain_for_sta(header):
    if header.section.section_num.startswith('B'):
        # We're in Annex B. Do we want to create this {alg_defn} and add it to {header}?
        if header.species.startswith('op: discriminated by syntax'):
            return False
            # These are additional/replacement units of
            # discriminated operations that are invoked in the main body,
            # so including them will mess up main-body semantics
            # until we can handle Annex B stuff properly.
        elif header.species in ['op: singular', 'bif: intrinsic']:
            return True
            # This is 2 ops (CharacterRangeOrUnion & CreateHTML) that are only
            # referenced from within Annex B,
            # plus a bunch of built-in functions.
            # So it doesn't hurt main-body semantics to include them.
            # (The reason to include them is that they are then
            # subjected to static type analysis.)
        else:
            assert 0, header.species
    else:
        # Main-body, so definitely include it.
        return True

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
                # This parameter doesn't have a param.decl_node.
                # That's because the algorithm doesn't have a structured header,
                # which happens for various reasons...
                #
                # - Built-in functions don't have structured headers,
                #   because they'd be uninformative,
                #   because every parameter is an ECMAScript language value,
                #   except when it's a spread parameter,
                #   when it's a List of ECMAScript language values.
                #
                # - Algorithms defined by <emu-eqn> (e.g., Day, TimeWithinDay)
                #   don't have structured headers
                #   because it wouldn't really fit the format?
                #
                # - In the memory model, algorithms that aren't abstract ops
                #   have parameters (sort of), but don't have a header that lists them.
                #
                # - Two Environment Record 'concrete methods' are never called,
                #   so they don't get a structured header.
                #     - (Object Env Rec).CreateImmutableBinding
                #     - (Module Env Rec).DeleteBinding
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
            # The for_phrase occurs in a <dt> of the <dl> of the structured header.
            # Maybe someday we'll parse that content,
            # in which case we'll get a {VAL_DESC} node.
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
            tnt = T_Tangible_ | T_tilde_empty_ | T_Reference_Record | T_Abrupt
            self.change_declared_type(tpn, tnt, tweak=True)

        # -------------------------

        self.started_with_TBD = set()

        for (pn, pt) in self.parameter_types.items():
            if pt == T_TBD:
                self.started_with_TBD.add(pn)

        if self.return_type == T_TBD:
            self.started_with_TBD.add('*return*')

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
            elif (
                self.species.startswith('bif:')
                or
                self.species == 'op: singular: host-defined'
                    # because HostMakeJobCallback has a default implementation
                or
                self.species == 'op: singular: implementation-defined'
                    # because PR #2781 introduced 3 with default implementations
            ):
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
        if self == T_MatcherContinuation:
            return "MatcherContinuation"
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
                'CaptureRange': {},
                'CharSet': {},
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
                },
                'Private Name': {},
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
                    'GraphLoadingState Record': {},
                    'ImportEntry Record': {},
                    'ImportMeta_record_': {},
                    'Intrinsics Record': {},
                    'Iterator Record': {},
                    'JSON Serialization Record': {},
                    'Job_record_': {},
                    'JobCallback Record': {},
                    'LoadedModule_Record_': {},
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
                'Relation': {},
                'Set': {},
                'Shared Data Block': {},
                    # The name suggests a subtype of Data Block,
                    # but doesn't seem to be treated that way.
                'SlotName_': {},
                'TypedArray_element_type': {
                    'tilde_Int8_': {},
                    'tilde_Uint8_': {},
                    'tilde_Uint8C_': {},
                    'tilde_Int16_': {},
                    'tilde_Uint16_': {},
                    'tilde_Int32_': {},
                    'tilde_Uint32_': {},
                    'tilde_BigInt64_': {},
                    'tilde_BigUint64_': {},
                    'tilde_Float32_': {},
                    'tilde_Float64_': {},
                },
                'WaiterList' : {},
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
                    'tilde_BigInt_': {},
                    'tilde_ConstructorMethod_': {},
                    'tilde_Fulfill_': {},
                    'tilde_Init_': {},
                    'tilde_NonConstructorMethod_': {},
                    'tilde_Number_': {},
                    'tilde_Reject_': {},
                    'tilde_SeqCst_': {},
                    'tilde_Unordered_': {},
                    'tilde_accessor_': {},
                    'tilde_all_': {},
                    'tilde_all_but_default_': {},
                    'tilde_ambiguous_': {},
                    'tilde_assignment_': {},
                    'tilde_asyncGenerator_': {},
                    'tilde_async_': {},
                    'tilde_async_iterate_': {},
                    'tilde_awaiting_return_': {},
                    'tilde_backward_': {},
                    'tilde_base_': {},
                    'tilde_completed_': {},
                    'tilde_derived_': {},
                    'tilde_empty_': {},
                    'tilde_end_': {},
                    'tilde_enumerate_': {},
                    'tilde_evaluated_': {},
                    'tilde_evaluating_': {},
                    'tilde_evaluating_async_': {},
                    'tilde_executing_': {},
                    'tilde_field_': {},
                    'tilde_forward_': {},
                    'tilde_frozen_': {},
                    'tilde_fulfilled_': {},
                    'tilde_generator_': {},
                    'tilde_global_': {},
                    'tilde_initialized_': {},
                    'tilde_invalid_': {},
                    'tilde_iterate_': {},
                    'tilde_key_': {},
                    'tilde_key_value_': {},
                    'tilde_lexicalBinding_': {},
                    'tilde_lexical_': {},
                    'tilde_lexical_this_': {},
                    'tilde_linked_': {},
                    'tilde_linking_': {},
                    'tilde_method_': {},
                    'tilde_namespace_': {},
                    'tilde_namespace_object_': {},
                    'tilde_new_': {},
                    'tilde_non_generator_': {},
                    'tilde_non_lexical_this_': {},
                    'tilde_normal_': {},
                    'tilde_number_': {},
                    'tilde_pending_': {},
                    'tilde_rejected_': {},
                    'tilde_sealed_': {},
                    'tilde_simple_': {},
                    'tilde_start_': {},
                    'tilde_start_end_': {},
                    'tilde_strict_': {},
                    'tilde_string_': {},
                    'tilde_suspendedStart_': {},
                    'tilde_suspendedYield_': {},
                    'tilde_symbol_': {},
                    'tilde_sync_': {},
                    'tilde_uninitialized_': {},
                    'tilde_unlinked_': {},
                    'tilde_unresolvable_': {},
                    'tilde_unused_': {},
                    'tilde_value_': {},
                    'tilde_varBinding_': {},
                },
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
        else:
            assert 0, type
        return TNode(type, tnode_for_type_[parent_type])
        # which has the side-effect of adding it to tnode_for_type_

ensure_tnode_for( ListType(T_other_) )
ensure_tnode_for( ProcType((), T_other_) )
ensure_tnode_for( ThrowType(T_other_) )

# ------------------------------------------------------------------------------

T_TBD = TBDType()

T_character_ = T_code_unit_ | T_code_point_

T_MathNonNegativeInteger_ = T_MathInteger_ # for now

T_MatcherContinuation = ProcType([T_MatchState                       ], T_MatchResult)
T_Matcher             = ProcType([T_MatchState, T_MatcherContinuation], T_MatchResult)
T_RegExpMatcher_  = ProcType([ListType(T_character_), T_MathNonNegativeInteger_], T_MatchResult)
T_Job             = ProcType([                       ], T_Tangible_ | T_tilde_empty_ | T_throw_)

T_ReadModifyWrite_modification_closure = ProcType([ListType(T_MathInteger_), ListType(T_MathInteger_)], ListType(T_MathInteger_))

T_captures_entry_ = T_CaptureRange | T_Undefined
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

    (_, sup_t) = type_bracket_for(nature_node, None)
    return sup_t

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

type_tweaks_tuples = [
    ('AsyncGeneratorEnqueue'                    , '_completion_'           , T_Abrupt | T_Normal   , T_Tangible_ | T_return_ | T_throw_),
    ('AsyncGeneratorUnwrapYieldResumption'      , '_resumptionValue_'      , T_Abrupt | T_Normal   , T_Tangible_ | T_return_ | T_throw_),
    ('AsyncIteratorClose'                       , '_completion_'           , T_Abrupt | T_Normal   , T_Tangible_ | T_tilde_empty_ | T_throw_),
    ('IteratorClose'                            , '_completion_'           , T_Normal | T_Abrupt   , T_Tangible_ | T_tilde_empty_ | T_throw_),
    ('MV'                                       , '*return*'               , T_TBD                 , T_MathInteger_),
    ('PromiseResolve'                           , '_C_'                    , T_constructor_object_ , T_Object),
    ('Day'                                      , '_t_'                    , T_TBD                 , T_FiniteNumber_ ),
    ('TimeWithinDay'                            , '_t_'                    , T_TBD                 , T_FiniteNumber_ ),
    ('DaysInYear'                               , '_y_'                    , T_TBD                 , T_FiniteNumber_ ),
    ('DayFromYear'                              , '_y_'                    , T_TBD                 , T_FiniteNumber_ ),
    ('TimeFromYear'                             , '_y_'                    , T_TBD                 , T_FiniteNumber_ ),
    ('YearFromTime'                             , '_t_'                    , T_TBD                 , T_FiniteNumber_ ),
    ('MonthFromTime'                            , '_t_'                    , T_TBD                 , T_FiniteNumber_ ),
    ('DateFromTime'                             , '_t_'                    , T_TBD                 , T_FiniteNumber_ ),
    ('WeekDay'                                  , '_t_'                    , T_TBD                 , T_FiniteNumber_ ),
    ('HourFromTime'                             , '_t_'                    , T_TBD                 , T_FiniteNumber_ ),
    ('MinFromTime'                              , '_t_'                    , T_TBD                 , T_FiniteNumber_ ),
    ('SecFromTime'                              , '_t_'                    , T_TBD                 , T_FiniteNumber_ ),
    ('msFromTime'                               , '_t_'                    , T_TBD                 , T_FiniteNumber_ ),
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
            elif expr_text == '« »':
                result_env = expr_env
            else:
                result_env = expr_env.with_expr_type_replaced(expr, expected_t)
        return result_env

    def ensure_A_can_be_element_of_list_B(self, item_ex, list_ex):
        (list_type, list_env) = tc_expr(list_ex, self)
        (item_type, item_env) = tc_expr(item_ex, list_env)

        if (list_type == T_List or list_type == ListType(T_TBD)) and item_type == T_TBD:
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

            if new_t.is_a_subtype_of_or_equal_to(old_t):
                # Narrowing expr's static type.
                # I.e., new_t is consistent with old_t,
                # it's just more precise (due to special info).
                pass
            elif old_t == T_TBD and new_t != T_TBD:
                # This is also a narrowing (sort of),
                # but it doesn't pass the previous test.
                pass
            elif (
                # These are cases where new_t is not a narrowing of old_t.
                # Some of these are perfectly normal,
                # some occur because STA isn't smart enough.

                old_t == T_not_passed and new_t != T_not_passed
                # This happens (in ToPrimitive and LoadRequestedModules)
                # when you have a step of the form:
                #     If _optional_ is not present, let _optional_ be <something>.
                # This already leads to other errors:
                #     re-Let on existing var `_optional_`. Use Set?
                #     ... also, this changes the type of var from not_passed to <something>

                or
                old_t == ListType(T_String) and new_t == ListType(T_String | T_Symbol)
                # This happens (in OrdinaryOwnPropertyKeys,
                # [[OwnPropertyKeys]] for a String exotic object, and
                # [[OwnPropertyKeys]] for an Integer-Indexed exotic object)
                # where (basically) we have:
                #     Let _keys_ be a new empty List.
                #     Append <string> to _keys_.
                #     Append <symbol> to _keys_.
                # After the first "Append", we infer that _keys_ is a List of Strings,
                # but after the second, we have to revise that.

                or
                old_t == ListType(T_Match_Record) and new_t == ListType(T_Match_Record | T_Undefined)
                # RegExpBuiltinExec
                # Similar to the preceding

                or
                old_t == ptn_type_for('AssignmentPattern') | T_not_set and new_t == T_Parse_Node
                # ForIn/OfBodyEvaluation.
                # STA isn't smart enough to know that _assignmentPattern_ *is* set.
                or
                old_t == T_Reference_Record | T_Tangible_ | T_tilde_empty_ and
                (
                    # STA for Evaluation is rough

                    new_t == T_Abrupt | old_t
                    # CaseBlockEvaluation
                    or
                    new_t == T_Private_Name | T_String | T_Symbol
                    # ClassFieldDefinitionEvaluation
                    or
                    new_t == ListType(T_code_unit_) | T_String | T_code_unit_
                    # Evaluation of SubstitutionTemplate
                )
                or
                old_t == T_String | T_Undefined and new_t == ListType(T_code_unit_) | T_String | T_code_unit_
                # Evaluation of SubstitutionTemplate, TemplateSpans, TemplateMiddleList
                # should maybe have an Assert that _head_/_tail_/_middle_ is a String (not *undefined*).
                or
                old_t == T_Proxy_exotic_object_ | T_bound_function_exotic_object_ | T_other_function_object_ and new_t == T_constructor_object_
                # MakeConstructor changes _F_ from a non-constructor to a constructor.
            ):
                # It's unclear whether it's worth posting an error for these.
                if 0:
                    add_pass_error(
                        expr,
                        f"Replacing type {old_t} with {new_t} is not a narrowing"
                    )
            else:
                stderr()
                stderr("with_expr_type_replaced")
                stderr("expr :", expr_text)
                stderr("old_t:", old_t)
                stderr("new_t:", new_t)
                assert 0
                # sys.exit(0)
        else:
            # expr_text not in self.vars
            assert expr_text in [
                '_e_.[[LocalName]]', # ResolveExport
                '_ee_.[[LocalName]]',
                '_scriptRecord_.[[Realm]]',
                '_srcBuffer_.[[ArrayBufferData]]', # %TypedArray%.prototype.set
                '_targetBuffer_.[[ArrayBufferData]]', # %TypedArray%.prototype.set
                '%GeneratorFunction.prototype.prototype.next%',
                '\u211d(_m_)', # MakeDay
                'WeekDay(_tv_)', # Date.prototype.toUTCString
                'MonthFromTime(_tv_)',
                '\u211d(_n_)', # unescape
                '_m_.[[CycleRoot]]', # GatherAsyncParentCompletions
                'ReferencedBindings of |NamedExports|',
                'PrototypePropertyNameList of |ClassElementList|',
                '\u211d(_m_) / 12', # MakeDay
                '\u211d(_number_)', # ToUint8Clamp
                'NormalCompletion(_value_)', # Await
            ], expr_text.encode('unicode_escape')
            if 0:
                add_pass_error(
                    expr,
                    f"`{expr_text}` not in self.vars, setting its type to {new_t}"
                )
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
        if expr.source_text() in ['_highest_', '_lowest_'] and expr_t == T_NegInfinityNumber_ | T_PosInfinityNumber_:
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
        # The caller is handling a {CONDITION} that hinges on whether
        # the value of `expr` is in a target set of values
        # (represented by `target_t`, in a way that's explained below).
        # This method returns a pair of Envs (each consistent with `self`):
        # one that holds whenever the condition is true, and
        # one that holds whenever the condition is false.
        #
        # In general, `target_t` is a pair of static types (sub_t, sup_t)
        # that 'bracket' the target set of values.
        #   I.e., sub_t <= target-set <= sup_t
        #   (where we interpret a static type as a set of values,
        #   and '<=' means 'is a subset of').
        # 
        # (When there's a static type whose set of values exactly matches the target set,
        # then sub_t == sup_t, and `target_t` can be just that type,
        # rather than a pair of types.)

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

        if isinstance(target_t, Type):
            sub_t = target_t
            sup_t = target_t
        else:
            (sub_t, sup_t) = target_t
            assert isinstance(sub_t, Type)
            assert isinstance(sup_t, Type)

        assert sup_t != T_TBD
        assert sub_t != T_TBD

        if asserting and expr_t == T_TBD:
            if copula == 'is a':
                true_env = env1.copy()
                true_env.vars[expr_text] = sup_t
                false_env = None
                return (true_env, false_env)
            else:
                # XXX wah
                return (env1, env1)

            # pdb.set_trace()

        (part_inside_sup_t, part_outside_sup_t) = expr_t.split_by(sup_t)
        assert isinstance(part_outside_sup_t, Type)
        assert isinstance(part_inside_sup_t, Type)

        (part_inside_sub_t, part_outside_sub_t) = expr_t.split_by(sub_t)
        assert isinstance(part_outside_sub_t, Type)
        assert isinstance(part_inside_sub_t, Type)

        # sub_t is often T_0, in which case
        # part_inside_sub_t == T_0
        # part_outside_sub_t == expr_t

        if asserting:
            if copula == 'is a':
                # We are asserting that the value of `expr` is in the target set of values.
                # For that to be possible, expr_t must have some intersection with sup_t.
                if part_inside_sup_t == T_0:
                    add_pass_error(
                        expr,
                        "ST of `%s` is `%s`, so can't be a `%s`"
                        % (expr_text, expr_t, sup_t)
                    )

                if part_outside_sup_t != T_0:
                    add_pass_error(
                        expr,
                        "STA fails to confirm that %s is a %s; could also be %s" %
                        (expr_text, sup_t, part_outside_sup_t)
                    )
                    # e.g. a parameter type starts as TBD.
                    # but because the Assert will only propagate the 'true' env,
                    # this error will probably disappear in a later pass.


            elif copula == 'isnt a':
                # We are asserting that the value of `expr` is NOT in the target set of values.
                # For that to be possible, expr_t must have no intersection with sub_t.
                if part_inside_sub_t != T_0:
                    add_pass_error(
                        expr,
                        "ST of `%s` is `%s`, so can't confirm the assertion -- value might be `%s`"
                        % (expr_text, expr_t, part_inside_sub_t)
                    )
                assert part_outside_sub_t != T_0
            else:
                assert 0, copula

        else:
            # Outside of an assertion,
            # you're presumably doing the type-test
            # with the expectation that either outcome is possible.
            if part_outside_sub_t == T_0:
                add_pass_error(
                    expr,
                    # XXX "static type is X, so must be Y"
                    "STA indicates that it's unnecessary to test whether `%s` is %s, because it must be" % (
                        expr_text, sub_t)
                )
                # ResolveExport _starResolution_ loop thing

            if part_inside_sup_t == T_0:
                add_pass_error(
                    expr,
                    # XXX "static type is X, so can't be Y"
                    "STA indicates that it's unnecessary to test whether `%s` is %s, because it can't be" % (
                        expr_text, sup_t)
                )
                # Perhaps a parameter-type was too restrictive.

        is_env   = env1.copy()
        isnt_env = env1.copy()
        is_env  .vars[expr_text] = part_inside_sup_t
        isnt_env.vars[expr_text] = part_outside_sub_t

        if copula == 'is a':
            return (is_env, isnt_env)
        elif copula == 'isnt a':
            return (isnt_env, is_env)
        else:
            assert 0, copula

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
        time.sleep(0.5)
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
            print("---> %s : %s" % (var_name, env.vars.get(var_name, "(not in env)")))

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
        expected_return_type = T_Tangible_ | T_throw_ | T_tilde_empty_
        # T_tilde_empty_ shouldn't really be allowed,
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

            if init_t == final_t: continue

            if pn in tah.started_with_TBD:
                # Change it.
                if trace_this_op:
                    print(f"About to change the declared_type of {pn} to {final_t}")
                    input('hit return to continue ')

                tah.change_declared_type(pn, final_t)

                changed_op_info = True

            else:
                # Don't change it.
                # But maybe convey that STA wants to change it.

                # Note that final_env is the env at the end of the algorithm
                # (i.e., the union of envs at the return points).
                # But its type for {pn} might legitimately be
                # wider or narrower than {pn}'s declared type,
                # if there are steps that overwrite ('Set') the value of {pn}.

                # E.g., if _x_ is declared as "(optional) Foo"
                # and there's a step
                #     "If _x_ is absent, then set _x_ to some Foo."
                # then at the end of the algorithm, the static type of _x_ will be just Foo.
                # But we shouldn't suggest removing "(optional)" from the declared type of _x_.
                #
                # You could construct a similar example for widening,
                # but I'm not sure it ever occurs in practice.

                if final_t.is_a_subtype_of_or_equal_to(init_t):
                    continue
                    level = 'info'
                    verbing = "narrowing"
                elif init_t.is_a_subtype_of_or_equal_to(final_t):
                    level = "warning"
                    verbing = "widening"
                else:
                    level = "warning"
                    verbing = "changing"

                # It's a warning when it's suggesting that there's a spec bug.

                add_pass_error(
                    tah.fake_node_for_[pn],
                    f"{level}: STA suggests {verbing} the type of {pn} to {final_t}"
                )

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
        if op_name in ['ToObject', 'RequireObjectCoercible']:
            # not ToBigInt
            assert isinstance(discriminator, NamedType)
            # in_env = init_env.with_expr_type_narrowed('_argument_', discriminator)
            in_env = init_env.copy()
            in_env.vars['_argument_'] = discriminator
        else:
            in_env = init_env

        if body.prod.lhs_s in ['{EMU_ALG_BODY}', '{IND_COMMANDS}', '{EE_RULE}', '{ONE_LINE_ALG}']:
            result = tc_nonvalue(body, in_env)
            assert result is None
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

            if pn == '*return*' and T_not_returned.is_a_subtype_of_or_equal_to(ptype) and ptype != T_Abrupt | ListType(T_code_unit_) | T_Reference_Record | T_Tangible_ | T_tilde_empty_ | T_not_returned:
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

    if p not in nv:
        stderr()
        stderr("tc_nonvalue:")
        stderr('    @nv.put(%s)' % escape(p))
        sys.exit(0)

    result = nv[p](anode, env0)

    assert result is None or isinstance(result, Env)

    if trace_this_op:
        print()
        print("Leaving nv:", trace_line)
        mytrace(result)

    return result

if 1:
    nv = DecoratedFuncDict()

    @nv.put(r'{IND_COMMANDS} : {_indent_}{COMMANDS}{_outdent_}')
    @nv.put(r'{COMMANDS} : {_NL_N} {COMMAND}')
    @nv.put(r'{COMMAND} : {IF_CLOSED}')
    @nv.put(r'{COMMAND} : {IF_OTHER}')
    @nv.put(r'{ELSE_PART} : Else, {SMALL_COMMAND}.')
    @nv.put(r'{ELSE_PART} : Else,{IND_COMMANDS}')
    @nv.put(r'{ELSE_PART} : Otherwise, {SMALL_COMMAND}.')
    @nv.put(r"{COMMAND} : Perform the following substeps in an implementation-defined order, possibly interleaving parsing and error detection:{IND_COMMANDS}")

    @nv.put(r"{COMMAND} : Optionally, {SMALL_COMMAND}.")
    @nv.put(r"{ONE_LINE_ALG} : {_indent_}{nlai}{COMMAND}{_outdent_}{nlai}")
    def _(anode, env0):
        [child] = anode.children
        return tc_nonvalue(child, env0)

    @nv.put(r"{COMMAND} : Find a finite time value {var} such that {CONDITION}; but if this is not possible (because some argument is out of range), return {LITERAL}.")
    def _(anode, env0):
        [var, cond, literal] = anode.children
        # once, in MakeDay
        env0.assert_expr_is_of_type(literal, T_Number)
        env1 = env0.plus_new_entry(var, T_FiniteNumber_)
        (t_env, f_env) = tc_cond(cond, env1)
        proc_add_return(env1, T_Number, literal)
        return env1

    # ---
    # parse

    @nv.put(r"{COMMAND} : Parse {PP_NAMED_OPERATION_INVOCATION} as a JSON text as specified in ECMA-404. Throw a {ERROR_TYPE} exception if it is not a valid JSON text as defined in that specification.")
    def _(anode, env0):
        [noi, error_type] = anode.children
        env0.assert_expr_is_of_type(noi, T_Unicode_code_points_)
        return env0

    if 1:

        # ------------------------
        # property keys of an object:

        @nv.put(r"{EACH_THING} : property of the Global Object specified in clause {h_emu_xref}")
        def _(each_thing, env0):
            [emu_xref] = each_thing.children
            # no loop_var!
            return env0

        # -----------------------
        # other collections:

    @nv.put(r'{COMMAND} : Once a generator enters the {tilded_word} state it never leaves it and its associated execution context is never resumed. Any execution state associated with {var} can be discarded at this point.')
    def _(anode, env0):
        [tw, var] = anode.children
        assert tw.source_text() == '~completed~'
        env0.assert_expr_is_of_type(var, T_Object)
        return env0

    # ----------------------------------

    @nv.put(r'{COMMAND} : Wait until no agent is in the critical section for {var}, then enter the critical section for {var} (without allowing any other agent to enter).')
    def _(anode, env0):
        [var1, var2] = anode.children
        [var_name1] = var1.children
        [var_name2] = var2.children
        assert var_name1 == var_name2
        env1 = env0.ensure_expr_is_of_type(var1, T_WaiterList)
        return env1

    @nv.put(r'{COMMAND} : Leave the critical section for {var}.')
    def _(anode, env0):
        [var] = anode.children
        env0.assert_expr_is_of_type(var, T_WaiterList)
        return env0

    @nv.put(r"{COMMAND} : Perform {PP_NAMED_OPERATION_INVOCATION} and suspend {var} for up to {var} milliseconds, performing the combined operation in such a way that a notification that arrives after the critical section is exited but before the suspension takes effect is not lost. {var} can wake from suspension either because the timeout expired or because it was notified explicitly by another agent calling NotifyWaiter with arguments {var} and {var}, and not for any other reasons at all.")
    def _(anode, env0):
        [noi, w_var, t_var, *blah] = anode.children
        env0.assert_expr_is_of_type(noi, T_tilde_unused_)
        env0.assert_expr_is_of_type(w_var, T_agent_signifier_)
        env0.assert_expr_is_of_type(t_var, T_MathReal_ | T_MathPosInfinity_)
        return env0

    @nv.put(r"{COMMAND} : IfAbruptRejectPromise({var}, {var}).")
    def _(anode, env0):
        [vara, varb] = anode.children
        env0.assert_expr_is_of_type(varb, T_PromiseCapability_Record)
        (ta, tenv) = tc_expr(vara, env0); assert tenv is env0

        env0.assert_expr_is_of_type(vara, T_Top_)
        (normal_part_of_ta, abnormal_part_of_ta) = ta.split_by(T_Normal)

        proc_add_return(env0, T_Promise_object_, anode)
        return env0.with_expr_type_narrowed(vara, normal_part_of_ta)

    @nv.put(r"{COMMAND} : Perform an implementation-defined debugging action.")
    def _(anode, env0):
        [] = anode.children
        return env0

    # -----

    @nv.put(r"{COMMAND} : Remove {var} from the list of waiters in {var}.")
    def _(anode, env0):
        [sig, wl] = anode.children
        env0.assert_expr_is_of_type(sig, T_agent_signifier_)
        env0.assert_expr_is_of_type(wl, T_WaiterList)
        return env0

    @nv.put(r"{COMMAND} : Notify the agent {var}.")
    def _(anode, env0):
        [var] = anode.children
        env0.assert_expr_is_of_type(var, T_agent_signifier_)
        return env0

    @nv.put(r"{COMMAND} : The code points `/` or any {nonterminal} occurring in the pattern shall be escaped in {var} as necessary to ensure that the string-concatenation of {EX}, {EX}, {EX}, and {EX} can be parsed (in an appropriate lexical context) as a {nonterminal} that behaves identically to the constructed regular expression. For example, if {var} is {STR_LITERAL}, then {var} could be {STR_LITERAL} or {STR_LITERAL}, among other possibilities, but not {STR_LITERAL}, because `///` followed by {var} would be parsed as a {nonterminal} rather than a {nonterminal}. If {var} is the empty String, this specification can be met by letting {var} be {STR_LITERAL}.")
    def _(anode, env0):
        # XXX
        return env0

    @nv.put(r"{COMMAND} : Remove from {var} all characters corresponding to a code point on the right-hand side of the {nonterminal} production.")
    def _(anode, env0):
        [var, nont] = anode.children
        env0.assert_expr_is_of_type(var, T_CharSet)
        return env0

    @nv.put(r"{COMMAND} : Attempt to parse {var} using {var} as the goal symbol, and analyse the parse result for any early error conditions. Parsing and early error detection may be interleaved in an implementation-defined manner.")
    def _(anode, env0):
        [text_var, goal_var] = anode.children
        env0.assert_expr_is_of_type(text_var, T_Unicode_code_points_)
        env0.assert_expr_is_of_type(goal_var, T_grammar_symbol_)
        return env0

    @nv.put(r"{COMMAND} : Sort {var} using an implementation-defined sequence of {h_emu_meta_start}calls to {var}{h_emu_meta_end}. If any such call returns an abrupt completion, stop before performing any further calls to {var} and return that Completion Record.")
    def _(anode, env0):
        [var, _, comparator, _, comparator] = anode.children
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_Tangible_))
        return env1

# ------------------------------------------------------------------------------

def tc_cond(cond, env0, asserting=False):
    # returns a tuple of two envs, one for true and one for false

    p = str(cond.prod)

    if trace_this_op:
        print()
        print("Entering c:", p)
        print("           ", cond.source_text())
        mytrace(env0)

    if p not in condd:
        stderr()
        stderr("tc_cond:")
        stderr('    @condd.put(%s)' % escape(p))
        sys.exit(0)

    result = condd[p](cond, env0, asserting)

    assert isinstance(result, tuple)
    assert len(result) == 2
    assert isinstance(result[0], Env)
    assert isinstance(result[1], Env) or result[1] is None

    if trace_this_op:
        print()
        print("Leaving c:", p)
        print("          ", cond.source_text())
        mytrace(result[0])

    return result

if 1:
    condd = DecoratedFuncDict()

    # ---

    @condd.put(r"{CONDITION_1} : {var} and {var} are both WriteSharedMemory or ReadModifyWriteSharedMemory events")
    def _(cond, env0, asserting):
        # XXX spec is ambiguous: "each is A or B" vs "either both A or both B"
        [ea, eb] = cond.children
        (a_t_env, a_f_env) = env0.with_type_test(ea, 'is a', T_WriteSharedMemory_event | T_ReadModifyWriteSharedMemory_event, asserting)
        (b_t_env, b_f_env) = env0.with_type_test(eb, 'is a', T_WriteSharedMemory_event | T_ReadModifyWriteSharedMemory_event, asserting)
        return (
            env_and(a_t_env, b_t_env),
            env_or(a_f_env, b_f_env)
        )

    # --------------------------------------------------
    # relating to strict code:

    @condd.put(r"{CONDITION_1} : the source text matched by {PROD_REF} is contained in strict mode code")
    @condd.put(r"{CONDITION_1} : the source text matched by {PROD_REF} is strict mode code")
    @condd.put(r"{CONDITION_1} : the source text matched by {var} is non-strict code")
    def _(cond, env0, asserting):
        [prod_ref] = cond.children
        env0.assert_expr_is_of_type(prod_ref, T_Parse_Node)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : the source text matched by the syntactic production that is being evaluated is contained in strict mode code")
    def _(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

    # -------------------------------------------------
    # introduce metavariable:

    @condd.put(r'{CONDITION_1} : there does not exist a member {var} of {var} such that {CONDITION_1}')
    @condd.put(r'{CONDITION_1} : there exists a member {var} of {var} such that {CONDITION_1}')
    def _(cond, env0, asserting):
        [member_var, set_var, stcond] = cond.children
        env1 = env0.ensure_expr_is_of_type(set_var, T_CharSet)
        env2 = env1.plus_new_entry(member_var, T_character_)
        (t_env, f_env) = tc_cond(stcond, env2)
        assert t_env is f_env
        return (env1, env1)

    @condd.put(r"{CONDITION_1} : there exists a WriteSharedMemory or ReadModifyWriteSharedMemory event {var} that has {var} in its range such that {CONDITION_1}")
    def _(cond, env0, asserting):
        [let_var, i, stcond] = cond.children
        env0.assert_expr_is_of_type(i, T_MathInteger_)
        env_for_cond = env0.plus_new_entry(let_var, T_WriteSharedMemory_event | T_ReadModifyWriteSharedMemory_event)
        return tc_cond(stcond, env_for_cond)

    @condd.put(r"{CONDITION_1} : there exists an event {var} such that {CONDITION}")
    def _(cond, env0, asserting):
        [let_var, stcond] = cond.children
        env_for_cond = env0.plus_new_entry(let_var, T_Shared_Data_Block_event)
        return tc_cond(stcond, env_for_cond)

    # --------------------------------------------------
    # whatever

    @condd.put(r'{CONDITION_1} : the file {h_a} of the Unicode Character Database provides a simple or common case folding mapping for {var}')
    def _(cond, env0, asserting):
        [h_a, var] = cond.children
        assert h_a.source_text() == '<a href="https://unicode.org/Public/UCD/latest/ucd/CaseFolding.txt"><code>CaseFolding.txt</code></a>'
        env1 = env0.ensure_expr_is_of_type(var, T_character_)
        return (env1, env1)

    @condd.put(r'{CONDITION_1} : {var} does not contain exactly one character')
    def _(cond, env0, asserting):
        [var] = cond.children
        env1 = env0.ensure_expr_is_of_type(var, T_CharSet)
        return (env1, env1)

    @condd.put(r'{CONDITION_1} : the Directive Prologue of {PROD_REF} contains a Use Strict Directive')
    def _(cond, env0, asserting):
        [prod_ref] = cond.children
        # XXX check that prod_ref makes sense
        return (env0, env0)

    @condd.put(r'{CONDITION_1} : The surrounding agent is not in the critical section for any WaiterList')
    def _(cond, env0, asserting):
        # nothing to check
        return (env0, env0)

    @condd.put(r'{CONDITION_1} : The surrounding agent is in the critical section for {var}')
    def _(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_WaiterList)
        return (env0, env0)

    @condd.put(r'{CONDITION_1} : {var} has a numeric value less than {code_unit_lit}')
    def _(cond, env0, asserting):
        [var, code_unit_lit] = cond.children
        env1 = env0.ensure_expr_is_of_type(var, T_code_point_) # odd
        return (env1, env1)

    @condd.put(r"{CONDITION_1} : {var} and {var} are the same Module Record")
    @condd.put(r"{CONDITION_1} : {var} and {DOTTING} are the same Module Record")
    @condd.put(r"{CONDITION_1} : {DOTTING} and {DOTTING} are not the same Module Record")
    def _(cond, env0, asserting):
        [ex1, ex2] = cond.children
        env0.assert_expr_is_of_type(ex1, T_Module_Record)
        env0.assert_expr_is_of_type(ex2, T_Module_Record)
        return (env0, env0)

    @condd.put(r'{CONDITION_1} : {var} has {var} in its range')
    def _(cond, env0, asserting):
        [sdbe_var, loc_var] = cond.children
        env1 = env0.ensure_expr_is_of_type(sdbe_var, T_Shared_Data_Block_event)
        env2 = env1.ensure_expr_is_of_type(loc_var, T_MathInteger_)
        return (env2, env2)

    @condd.put(r'{CONDITION_1} : {EX} is in {EX}')
    @condd.put(r'{CONDITION_1} : {var} is not in {var}')
    @condd.put(r'{CONDITION_1} : {var} occurs exactly once in {var}')
    def _(cond, env0, asserting):
        [item_var, container_var] = cond.children
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

    @condd.put(r'{CONDITION_1} : There are sufficient bytes in {var} starting at {var} to represent a value of {var}')
    def _(cond, env0, asserting):
        [ab_var, st_var, t_var] = cond.children
        env0.assert_expr_is_of_type(ab_var, T_ArrayBuffer_object_ | T_SharedArrayBuffer_object_)
        env0.assert_expr_is_of_type(st_var, T_MathInteger_)
        env0.assert_expr_is_of_type(t_var, T_TypedArray_element_type)
        return (env0, env0)

    @condd.put(r'{CONDITION_1} : {var} is on the list of waiters in {var}')
    def _(cond, env0, asserting):
        [w_var, wl_var] = cond.children
        env0.assert_expr_is_of_type(w_var, T_agent_signifier_)
        env0.assert_expr_is_of_type(wl_var, T_WaiterList)
        return (env0, env0)

    @condd.put(r'{CONDITION_1} : {var} was notified explicitly by another agent calling NotifyWaiter with arguments {var} and {var}')
    def _(cond, env0, asserting):
        [w_var, *blah] = cond.children
        env0.assert_expr_is_of_type(w_var, T_agent_signifier_)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : We've reached the starting point of an `export *` circularity")
    def _(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {var} provides the direct binding for this export")
    def _(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_Source_Text_Module_Record)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {var} imports a specific binding for this export")
    def _(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_Source_Text_Module_Record)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : This is a circular import request")
    def _(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : A `default` export was not explicitly defined by this module")
    def _(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : There is more than one `*` import that includes the requested name")
    def _(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : we return here")
    def _(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : the async function either threw an exception or performed an implicit or explicit return; all awaiting is done")
    def _(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : the async generator either threw an exception or performed either an implicit or explicit return")
    def _(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {var} binds a single name")
    def _(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : the generator either threw an exception or performed either an implicit or explicit return")
    def _(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : an implementation-defined debugging facility is available and enabled")
    def _(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : All named exports from {var} are resolvable")
    def _(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_Source_Text_Module_Record)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : Evaluate has already been invoked on {var} and successfully completed")
    def _(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_Module_Record)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : the character {EX} is one of {nonterminal}")
    def _(cond, env0, asserting):
        [ex, nonterminal] = cond.children
        env0.assert_expr_is_of_type(ex, T_character_)
        assert nonterminal.source_text() == '|LineTerminator|'
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {PP_NAMED_OPERATION_INVOCATION} is not the same character value as {PP_NAMED_OPERATION_INVOCATION}")
    def _(cond, env0, asserting):
        [anoi, bnoi] = cond.children
        env0.assert_expr_is_of_type(anoi, T_character_)
        env0.assert_expr_is_of_type(bnoi, T_character_)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {var} does not contain a valid UTF-8 encoding of a Unicode code point")
    def _(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, ListType(T_MathInteger_))
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {var} and {var} each contain exactly one character")
    def _(cond, env0, asserting):
        [a,b] = cond.children
        env0.assert_expr_is_of_type(a, T_CharSet)
        env0.assert_expr_is_of_type(b, T_CharSet)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {var} contains any {nonterminal}")
    def _(cond, env0, asserting):
        [rvar, nonterminal] = cond.children
        env0.assert_expr_is_of_type(rvar, T_Object)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : the {var}<sup>th</sup> capture of {var} was defined with a {nonterminal}")
    def _(cond, env0, asserting):
        [ivar, rvar, nonterminal] = cond.children
        env0.assert_expr_is_of_type(ivar, T_MathInteger_)
        env0.assert_expr_is_of_type(rvar, T_Object)
        return (env0, env0)

    # ----

    @condd.put(r"{CONDITION_1} : {var} is not on the list of waiters in any WaiterList")
    def _(cond, env0, asserting):
        [sig_var] = cond.children
        env0.assert_expr_is_of_type(sig_var, T_agent_signifier_)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {var} is not on the list of waiters in {var}")
    def _(cond, env0, asserting):
        [sig_var, wl_var] = cond.children
        env0.assert_expr_is_of_type(sig_var, T_agent_signifier_)
        env0.assert_expr_is_of_type(wl_var, T_WaiterList)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : GlobalSymbolRegistry does not currently contain an entry for {var}")
    def _(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_String | T_Symbol)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : only one argument was passed")
    def _(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {var} and {var} are in a race in {var}")
    def _(cond, env0, asserting):
        [ea, eb, exe] = cond.children
        env0.assert_expr_is_of_type(ea, T_Shared_Data_Block_event)
        env0.assert_expr_is_of_type(eb, T_Shared_Data_Block_event)
        env0.assert_expr_is_of_type(exe, T_candidate_execution)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {var} and {var} do not have disjoint ranges")
    @condd.put(r"{CONDITION_1} : {var} and {var} have equal ranges")
    @condd.put(r"{CONDITION_1} : {var} and {var} have overlapping ranges")
    def _(cond, env0, asserting):
        [ea, eb] = cond.children
        env0.assert_expr_is_of_type(ea, T_Shared_Data_Block_event)
        env0.assert_expr_is_of_type(eb, T_Shared_Data_Block_event)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {EX} is not {var}")
    def _(cond, env0, asserting):
        [ea, eb] = cond.children
        # over-specific:
        env0.assert_expr_is_of_type(ea, T_Shared_Data_Block_event | T_host_defined_ | T_Undefined)
        env0.assert_expr_is_of_type(eb, T_Shared_Data_Block_event | T_host_defined_ | T_Undefined)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {EX} is listed in the “Code Point” column of {h_emu_xref}")
    def _(cond, env0, asserting):
        [ex, emu_xref] = cond.children
        env0.assert_expr_is_of_type(ex, T_code_point_)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {var} has the same numeric value as a {h_emu_xref} or {h_emu_xref}")
    def _(cond, env0, asserting):
        [var, emu_xref1, emu_xref2] = cond.children
        env0.assert_expr_is_of_type(var, T_code_point_)
        return (env0, env0)

    # PR ? function-strictness
    @condd.put(r"{CONDITION_1} : the source text matched by {var} is strict mode code")
    def _(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {var} is not a {h_emu_xref} or {h_emu_xref}")
    def _(cond, env0, asserting):
        [var, xrefa, xrefb] = cond.children
        assert xrefa.source_text() == '<emu-xref href="#leading-surrogate"></emu-xref>'
        assert xrefb.source_text() == '<emu-xref href="#trailing-surrogate"></emu-xref>'
        env0.assert_expr_is_of_type(var, T_code_unit_)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {var} has a Synchronize event")
    def _(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_WaiterList)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {var} does not provide the direct binding for this export")
    def _(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_Module_Record)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {PP_NAMED_OPERATION_INVOCATION} contains any code points other than {backticked_word}, {backticked_word}, {backticked_word}, {backticked_word}, {backticked_word}, {backticked_word}, or {backticked_word}, or if it contains the same code point more than once")
    def _(cond, env0, asserting):
        [noi, *bw_] = cond.children
        env0.assert_expr_is_of_type(noi, T_Unicode_code_points_)
        for bw in bw_:
            assert len(bw.source_text()) == 3 # single-character 'words'
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {PP_NAMED_OPERATION_INVOCATION} contains {backticked_word}")
    def _(cond, env0, asserting):
        [noi, bw] = cond.children
        env0.assert_expr_is_of_type(noi, T_Unicode_code_points_)
        assert len(bw.source_text()) == 3 # single-character 'word'
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : the parse succeeded and no early errors were found")
    def _(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {NAMED_OPERATION_INVOCATION} is the same String value as the StringValue of any |ReservedWord| except for `yield` or `await`")
    def _(cond, env0, asserting):
        [noi] = cond.children
        env0.assert_expr_is_of_type(noi, T_String)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {LOCAL_REF} is contained in strict mode code")
    def _(cond, env0, asserting):
        [local_ref] = cond.children
        env0.assert_expr_is_of_type(local_ref, T_Parse_Node)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : the source text containing {G_SYM} is eval code that is being processed by a direct eval")
    def _(cond, env0, asserting):
        [g_sym] = cond.children
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : the source text matched by {PROD_REF} is not a Unicode property name or property alias listed in the “Property name and aliases” column of {h_emu_xref}")
    def _(cond, env0, asserting):
        [prod_ref, h_emu_xref] = cond.children
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : the source text matched by {PROD_REF} is not a Unicode property value or property value alias for the General_Category (gc) property listed in {h_a}, nor a binary property or binary property alias listed in the “Property name and aliases” column of {h_emu_xref}")
    def _(cond, env0, asserting):
        [prod_ref, h_a, h_emu_xref] = cond.children
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : the source text matched by {PROD_REF} is not a property value or property value alias for the Unicode property or property alias given by the source text matched by {PROD_REF} listed in {h_a}")
    def _(cond, env0, asserting):
        [prod_refa, prod_refb, h_a] = cond.children
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : the name is used once for a getter and once for a setter and in no other entries, and the getter and setter are either both static or both non-static")
    def _(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : This is only possible for getter/setter pairs")
    def _(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {DOTTING} is {LITERAL} and was never previously set to {LITERAL}")
    def _(cond, env0, asserting):
        [dotting, lita, litb] = cond.children
        assert lita.source_text() == '*false*'
        assert litb.source_text() == '*true*'
        env0.assert_expr_is_of_type(dotting, T_Boolean)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {var} has been linked and declarations in its module environment have been instantiated")
    def _(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_Source_Text_Module_Record)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : LoadRequestedModules has completed successfully on {var} prior to invoking this abstract operation")
    def _(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_Cyclic_Module_Record)
        return (env0, env0)

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

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

# type-bracket dict (unfortunately same initials as 'to be determined')
tbd = DecoratedFuncDict()

def type_bracket_for(vd, env):
    assert vd.prod.lhs_s in [
        '{VALUE_DESCRIPTION}',
        '{VAL_DESC}',
        '{LITERAL}',
        '{NUMBER_LITERAL}',
        '{MATH_LITERAL}',
        '{LIST_ELEMENTS_DESCRIPTION}',
    ], str(vd.prod)

    assert env is None or isinstance(env, Env)
    # It's None when {vd} comes from a parameter-decl or a field-decl.
    # It's an Env when {vd} comes from a condition in a step in an algorithm.

    vd_p = str(vd.prod)

    try:
        result = tbd[vd_p]
    except KeyError:
        stderr()
        stderr("No handler:")
        stderr(f"@tbd.put({vd_p!r})")
        stderr("or")
        stderr(f"tbd[{vd_p!r}] = ")
        sys.exit(1)

    if callable(result):
        result = result(vd, env)

    if isinstance(result, Type):
        # It's a type that exactly represents
        # the set of values described by {vd}.
        type_bracket = (result, result)
    elif len(result) == 2:
        assert isinstance(result[0], Type)
        assert isinstance(result[1], Type)
        type_bracket = result
    else:
        assert 0, result

    return type_bracket

# ------------------------------------------------------------------------------

def a_subset_of(t): return (T_0, t)

@tbd.put('{VALUE_DESCRIPTION} : {VAL_DESC}')
@tbd.put('{VAL_DESC} : {LITERAL}')
@tbd.put('{LITERAL} : {NUMBER_LITERAL}')
@tbd.put('{LITERAL} : {MATH_LITERAL}')
def _(vd, env):
    [child] = vd.children
    return type_bracket_for(child, env)

# ------------------

@tbd.put('{VAL_DESC} : a property value or property value alias for the Unicode property {var} listed in {h_a}')
def _(val_desc, env):
    [var, h_a] = val_desc.children
    env.assert_expr_is_of_type(var, T_Unicode_code_points_)
    return T_Unicode_code_points_

@tbd.put('{VAL_DESC} : an Abstract Closure that takes {VAL_DESC} and {VAL_DESC} and returns {VAL_DESC}')
def _(val_desc, env):
    assert val_desc.source_text() == 'an Abstract Closure that takes a List of characters and a non-negative integer and returns a MatchResult'
    return T_RegExpMatcher_

tbd['{VAL_DESC} : ECMAScript source text'] = T_Unicode_code_points_
tbd['{VAL_DESC} : a CharSet'] = T_CharSet
tbd['{VAL_DESC} : a Cyclic Module Record'] = T_Cyclic_Module_Record
tbd['{VAL_DESC} : a FinalizationRegistry'] = T_FinalizationRegistry_object_
tbd['{VAL_DESC} : a For-In Iterator'] = T_Iterator_object_
tbd['{VAL_DESC} : a Generator'] = a_subset_of(T_Iterator_object_)
tbd['{VAL_DESC} : a GraphLoadingState Record'] = T_GraphLoadingState_Record
tbd['{VAL_DESC} : a JSON Serialization Record'] = T_JSON_Serialization_Record
tbd['{VAL_DESC} : a Match Record'] = T_Match_Record
tbd['{VAL_DESC} : a MatchResult'] = T_MatchResult
tbd['{VAL_DESC} : a MatchState'] = T_MatchState
tbd['{VAL_DESC} : a Matcher'] = T_Matcher
tbd['{VAL_DESC} : a MatcherContinuation'] = T_MatcherContinuation
tbd['{VAL_DESC} : a Module Namespace Object'] = T_Object
tbd['{VAL_DESC} : a Module Record'] = T_Module_Record
tbd['{VAL_DESC} : a Promise'] = T_Promise_object_
tbd['{VAL_DESC} : a PromiseCapability Record for an intrinsic {percent_word}'] = T_PromiseCapability_Record
tbd['{VAL_DESC} : a PromiseCapability Record'] = T_PromiseCapability_Record
tbd['{VAL_DESC} : a PromiseReaction Record'] = T_PromiseReaction_Record
tbd['{VAL_DESC} : a ReadModifyWriteSharedMemory event'] = T_ReadModifyWriteSharedMemory_event
tbd['{VAL_DESC} : a ReadSharedMemory or ReadModifyWriteSharedMemory event'] = T_ReadSharedMemory_event | T_ReadModifyWriteSharedMemory_event
tbd['{VAL_DESC} : a ReadSharedMemory, WriteSharedMemory, or ReadModifyWriteSharedMemory event'] = T_Shared_Data_Block_event
tbd['{VAL_DESC} : a RegExp Record'] = T_RegExp_Record
tbd['{VAL_DESC} : a ResolvedBinding Record'] = T_ResolvedBinding_Record
tbd['{VAL_DESC} : a Script Record'] = T_Script_Record
tbd['{VAL_DESC} : a Set of events'] = T_Set
tbd['{VAL_DESC} : a SharedArrayBuffer'] = T_SharedArrayBuffer_object_
tbd['{VAL_DESC} : a Source Text Module Record'] = T_Source_Text_Module_Record
tbd['{VAL_DESC} : a String which is the name of a TypedArray constructor in {h_emu_xref}'] = a_subset_of(T_String)
tbd['{VAL_DESC} : a TypedArray element type'] = T_TypedArray_element_type
tbd['{VAL_DESC} : a TypedArray'] = T_TypedArray_object_
tbd['{VAL_DESC} : a UTF-16 code unit'] = T_code_unit_
tbd['{VAL_DESC} : a Unicode code point'] = T_code_point_
tbd['{VAL_DESC} : a Unicode property name or property alias listed in the “Property name and aliases” column of {h_emu_xref}'] = a_subset_of(T_Unicode_code_points_)
tbd['{VAL_DESC} : a Unicode property name'] = a_subset_of(T_Unicode_code_points_)
tbd['{VAL_DESC} : a Unicode property value or property value alias for the General_Category (gc) property listed in {h_a}'] = a_subset_of(T_Unicode_code_points_)
tbd['{VAL_DESC} : a Unicode property value'] = a_subset_of(T_Unicode_code_points_)
tbd['{VAL_DESC} : a Unicode {h_emu_not_ref_property_name} or property alias listed in the “{h_emu_not_ref_Property_name} and aliases” column of {h_emu_xref} or {h_emu_xref}'] = a_subset_of(T_Unicode_code_points_)
tbd['{VAL_DESC} : a WaiterList'] = T_WaiterList
tbd['{VAL_DESC} : a WeakRef'] = T_WeakRef_object_
tbd['{VAL_DESC} : a WriteSharedMemory event'] = T_WriteSharedMemory_event
tbd['{VAL_DESC} : a binary Unicode property or binary property alias listed in the “Property name and aliases” column of {h_emu_xref}'] = a_subset_of(T_Unicode_code_points_)
tbd['{VAL_DESC} : a candidate execution'] = T_candidate_execution
tbd['{VAL_DESC} : a candidate execution Record'] = T_candidate_execution
tbd['{VAL_DESC} : a canonical, unaliased Unicode property name listed in the “Canonical property name” column of {h_emu_xref}'] = a_subset_of(T_Unicode_code_points_)
tbd['{VAL_DESC} : a character'] = T_code_unit_ | T_code_point_
tbd['{VAL_DESC} : a code point'] = T_code_point_
tbd['{VAL_DESC} : a code unit'] = T_code_unit_
tbd['{VAL_DESC} : a finite time value'] = T_IntegralNumber_
tbd['{VAL_DESC} : a happens-before Relation'] = T_Relation
tbd['{VAL_DESC} : a host-synchronizes-with Relation'] = T_Relation
tbd['{VAL_DESC} : a read-modify-write modification function'] = T_ReadModifyWrite_modification_closure
tbd['{VAL_DESC} : a reads-bytes-from mathematical function'] = ProcType([T_event_], ListType(T_WriteSharedMemory_event | T_ReadModifyWriteSharedMemory_event))
tbd['{VAL_DESC} : a reads-from Relation'] = T_Relation
tbd['{VAL_DESC} : a sequence of Unicode code points'] = T_Unicode_code_points_
tbd['{VAL_DESC} : a synchronizes-with Relation'] = T_Relation
tbd['{VAL_DESC} : a time value'] = T_IntegralNumber_
tbd['{VAL_DESC} : an ArrayBuffer or SharedArrayBuffer'] = T_ArrayBuffer_object_ | T_SharedArrayBuffer_object_
tbd['{VAL_DESC} : an ArrayBuffer'] = T_ArrayBuffer_object_
tbd['{VAL_DESC} : an AsyncGenerator'] = T_AsyncGenerator_object_
tbd['{VAL_DESC} : an Iterator'] = T_Iterator_object_
tbd['{VAL_DESC} : an Object that conforms to the <i>IteratorResult</i> interface'] = a_subset_of(T_Object)
tbd['{VAL_DESC} : an agent-order Relation'] = T_Relation
tbd['{VAL_DESC} : an initialized RegExp instance'] = a_subset_of(T_Object)
tbd['{VAL_DESC} : an instance of a concrete subclass of Module Record'] = T_Module_Record
tbd['{VAL_DESC} : source text'] = T_Unicode_code_points_
tbd['{VAL_DESC} : the execution context of a generator'] = a_subset_of(T_execution_context)
tbd['{VAL_DESC} : the single code point {code_point_lit} or {code_point_lit}'] = a_subset_of(T_Unicode_code_points_)
tbd['{VAL_DESC} : {backticked_oth}'] = a_subset_of(T_Unicode_code_points_)

# Note re 'a time value':
# time value is defined to be 'IntegralNumber_ | NaN_Number_',
# but the only use is for UTC()'s return value,
# which is the result of a subtraction,
# so probably shouldn't be NaN.
# So I've translated it as T_IntegralNumber_.
# I.e., the spec should say "a *finite* time value".

# ------------------

@tbd.put('{LIST_ELEMENTS_DESCRIPTION} : {ERROR_TYPE} objects')
def _(led, env):
    [error_type] = led.children
    return type_for_ERROR_TYPE(error_type)

tbd['{LIST_ELEMENTS_DESCRIPTION} : Agent Events Records'               ] = T_Agent_Events_Record
tbd['{LIST_ELEMENTS_DESCRIPTION} : AsyncGeneratorRequest Records'      ] = T_AsyncGeneratorRequest_Record
tbd['{LIST_ELEMENTS_DESCRIPTION} : Chosen Value Records'               ] = T_Chosen_Value_Record
tbd['{LIST_ELEMENTS_DESCRIPTION} : Cyclic Module Records'              ] = T_Cyclic_Module_Record
tbd['{LIST_ELEMENTS_DESCRIPTION} : ExportEntry Records'                ] = T_ExportEntry_Record
tbd['{LIST_ELEMENTS_DESCRIPTION} : ImportEntry Records'                ] = T_ImportEntry_Record
tbd['{LIST_ELEMENTS_DESCRIPTION} : PromiseReaction Records'            ] = T_PromiseReaction_Record
tbd['{LIST_ELEMENTS_DESCRIPTION} : Source Text Module Records'         ] = T_Source_Text_Module_Record
tbd['{LIST_ELEMENTS_DESCRIPTION} : WriteSharedMemory or ReadModifyWriteSharedMemory events'] = T_WriteSharedMemory_event | T_ReadModifyWriteSharedMemory_event
tbd['{LIST_ELEMENTS_DESCRIPTION} : byte values'                        ] = a_subset_of(T_MathInteger_)
tbd['{LIST_ELEMENTS_DESCRIPTION} : characters'                         ] = T_character_
tbd['{LIST_ELEMENTS_DESCRIPTION} : code points'                        ] = T_code_point_
tbd['{LIST_ELEMENTS_DESCRIPTION} : either Match Records or *undefined*'] = T_Match_Record | T_Undefined
tbd['{LIST_ELEMENTS_DESCRIPTION} : either WriteSharedMemory or ReadModifyWriteSharedMemory events'] = T_WriteSharedMemory_event | T_ReadModifyWriteSharedMemory_event
tbd['{LIST_ELEMENTS_DESCRIPTION} : errors'                             ] = T_SyntaxError | T_ReferenceError
tbd['{LIST_ELEMENTS_DESCRIPTION} : events'                             ] = T_event_
tbd['{LIST_ELEMENTS_DESCRIPTION} : pairs of Synchronize events'        ] = T_event_pair_

# ------------------

tbd['{LITERAL} : {code_unit_lit}'] = a_subset_of(T_code_unit_)

# ------------------------------------------------------------------------------

def convert_nature_to_type(nature):
    fake_p = '{VAL_DESC} : ' + nature
    if fake_p in tbd:
        tb = tbd[fake_p]
        if isinstance(tb, Type):
            return tb
        elif len(tb) == 2:
            (_, sup_t) = tb
            return sup_t
        else:
            assert 0, tb

    else:
        return {
            # built-ins:
            'a List of ECMAScript language values': ListType(T_Tangible_),

            # emu-eqn:
            'unknown': T_TBD,

            # memory model:
            'an event in SharedDataBlockEventSet(_execution_)': T_Shared_Data_Block_event,

            # for phrase:
            'Parse Node': T_Parse_Node,

            'an immutable prototype exotic object': T_Object,

            'an execution': T_candidate_execution, # ???

            'a Declarative Environment Record': T_Declarative_Environment_Record,
            'a Function Environment Record': T_Function_Environment_Record,
            'a Global Environment Record': T_Global_Environment_Record,
            'a Module Environment Record': T_Module_Environment_Record,
            'an Object Environment Record': T_Object_Environment_Record,

            # record field type outside of <td>:
            '*null* or an Environment Record': T_Null | T_Environment_Record,
            'an Object or *undefined*': T_Object | T_Undefined,
            'a String or ~namespace~': T_String | T_tilde_namespace_,

        }[nature]

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

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
        if p not in exprd:
            stderr()
            stderr("tc_expr:")
            stderr('    @exprd.put(%s)' % escape(p))
            # pdb.set_trace()
            sys.exit(0)

        (expr_type, env1) = exprd[p](expr, env0, expr_value_will_be_discarded)

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

if 1:
    exprd = DecoratedFuncDict()

    @exprd.put(r"{EXPR} : the result of {PP_NAMED_OPERATION_INVOCATION}")
    @exprd.put(r"{EXPR} : {EX}")
    @exprd.put(r"{EX} : ({EX})")
    @exprd.put(r"{EX} : The value of {SETTABLE}")
    @exprd.put(r"{EX} : the value of {SETTABLE}")
    @exprd.put(r"{EX} : the {var} flag")
    @exprd.put(r"{EX} : {code_point_lit}")
    @exprd.put(r"{EX} : {LITERAL}")
    @exprd.put(r"{EX} : {LOCAL_REF}")
    @exprd.put(r"{EX} : {NUM_EXPR}")
    @exprd.put(r"{EX} : {PAIR}")
    @exprd.put(r"{EX} : {PP_NAMED_OPERATION_INVOCATION}")
    @exprd.put(r"{EX} : {RECORD_CONSTRUCTOR}")
    @exprd.put(r"{FACTOR} : ({NUM_EXPR})")
    @exprd.put(r"{FACTOR} : {BIGINT_LITERAL}")
    @exprd.put(r"{FACTOR} : {MATH_LITERAL}")
    @exprd.put(r"{FACTOR} : {NUMBER_LITERAL}")
    @exprd.put(r"{FACTOR} : {PP_NAMED_OPERATION_INVOCATION}")
    @exprd.put(r"{FACTOR} : {SETTABLE}")
    @exprd.put(r"{LITERAL} : {BIGINT_LITERAL}")
    @exprd.put(r"{LITERAL} : {MATH_LITERAL}")
    @exprd.put(r"{LITERAL} : {NUMBER_LITERAL}")
    @exprd.put(r"{LITERAL} : {code_unit_lit}")
    @exprd.put(r"{LOCAL_REF} : {PROD_REF}")
    @exprd.put(r"{LOCAL_REF} : {SETTABLE}")
    @exprd.put(r"{NAMED_OPERATION_INVOCATION} : {PREFIX_PAREN}")
    @exprd.put(r"{NUM_COMPARAND} : {FACTOR}")
    @exprd.put(r"{NUM_COMPARAND} : {SUM}")
    @exprd.put(r"{NUM_COMPARAND} : {PRODUCT}")
    @exprd.put(r"{NUM_EXPR} : {PRODUCT}")
    @exprd.put(r"{NUM_EXPR} : {SUM}")
    @exprd.put(r"{RHSS} : {RHS}")
    @exprd.put(r"{SETTABLE} : {DOTTING}")
    @exprd.put(r"{TERM} : {FACTOR}")
    @exprd.put(r"{TERM} : {PRODUCT}")
    @exprd.put(r"{TYPE_ARG} : {DOTTING}")
    @exprd.put(r"{TYPE_ARG} : {var}")
    def _(expr, env0, expr_value_will_be_discarded):
        [child] = expr.children
        return tc_expr(child, env0, expr_value_will_be_discarded)

    # -------------------------------------------------
    # return T_Number

    @exprd.put(r"{EXPR} : the Element Size value specified in {h_emu_xref} for Element Type {var}")
    def _(expr, env0, _):
        [emu_xref, var] = expr.children
        assert var.source_text() in ['_type_', '_srcType_', '_elementType_']
        env1 = env0.ensure_expr_is_of_type(var, T_TypedArray_element_type)
        return (T_MathInteger_, env1)

    @exprd.put(r"{EXPR} : the Element Size value specified in {h_emu_xref} for {EX}")
    def _(expr, env0, _):
        [emu_xref, ex] = expr.children
        env1 = env0.ensure_expr_is_of_type(ex, T_String)
        return (T_MathInteger_, env1)

    @exprd.put(r"{EXPR} : (({var} `*` msPerHour `+` {var} `*` msPerMinute) `+` {var} `*` msPerSecond) `+` {var}, performing the arithmetic according to IEEE 754-2019 rules (that is, as if using the ECMAScript operators `*` and `+`)")
    def _(expr, env0, _):
        for var in expr.children:
            env0.assert_expr_is_of_type(var, T_Number)
        return (T_Number, env0)

    # --------------------------------------------------------
    # return T_MathInteger_: The size of some collection:

    @exprd.put(r"{EXPR} : the number of elements in {var}'s _captures_ List")
    def _(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_MatchState)
        return (T_MathNonNegativeInteger_, env0)

    @exprd.put(r"{EXPR} : the number of non-optional parameters of the function definition in {h_emu_xref}")
    def _(expr, env0, _):
        [xref] = expr.children
        return (T_MathNonNegativeInteger_, env0)

    @exprd.put(r"{FACTOR} : {CONSTANT_NAME}")
    @exprd.put(r"{EX} : {CONSTANT_NAME}")
    def _(expr, env0, _):
        [constant_name] = expr.children
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

    @exprd.put(r"{NUM_COMPARAND} : the numeric value of {var}")
    @exprd.put(r"{EX} : the numeric value of {EX}")
    def _(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_code_unit_ | T_code_point_)
        return (T_MathInteger_, env1)

    # ----

    @exprd.put(r'{EXPR} : the character value of character {var}')
    def _(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_character_)
        return (T_MathInteger_, env0)

    @exprd.put(r"{EXPR} : the numeric value according to {h_emu_xref}")
    def _(expr, env0, _):
        return (T_MathInteger_, env0)

    @exprd.put(r"{EX} : {var}'s _endIndex_")
    @exprd.put(r"{EX} : {var}'s _endIndex_ value")
    @exprd.put(r"{NUM_COMPARAND} : {var}'s _endIndex_")
    def _(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_MatchState | T_CaptureRange)
        return (T_MathInteger_, env1)

    @exprd.put(r"{EX} : {var}'s _startIndex_")
    def _(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_CaptureRange)
        return (T_MathInteger_, env1)

    @exprd.put(r"{EXPR} : the index into {var} of the character that was obtained from element {EX} of {var}")
    def _(expr, env0, _):
        [list_var, index_var, str_var] = expr.children
        env0.assert_expr_is_of_type(list_var, T_List)
        env0.assert_expr_is_of_type(index_var, T_MathInteger_)
        env0.assert_expr_is_of_type(str_var, T_String) # todo: element of String
        return (T_MathInteger_, env0)

    @exprd.put(r"{EXPR} : the code point obtained by applying the UTF-8 transformation to {var}, that is, from a List of octets into a 21-bit value")
    def _(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, ListType(T_MathInteger_))
        return (T_code_point_, env0)

    # -------------------------
    # return T_String

    @exprd.put(r"{EXPR} : the Element Type value specified in {h_emu_xref} for {EX}")
    def _(expr, env0, _):
        [emu_xref, ex] = expr.children
        env1 = env0.ensure_expr_is_of_type(ex, T_String)
        return (T_TypedArray_element_type, env0)

    @exprd.put(r"{EXPR} : the Name of the entry in {h_emu_xref} with the Number {PP_NAMED_OPERATION_INVOCATION}")
    def _(expr, env0, _):
        [emu_xref, noi] = expr.children
        env1 = env0.ensure_expr_is_of_type(noi, T_IntegralNumber_)
        return (T_String, env1)

    @exprd.put(r"{EXPR} : an implementation-defined string that is either {EX} or {EXPR}")
    def _(expr, env0, _):
        [exa, exb] = expr.children
        env0.assert_expr_is_of_type(exa, T_String)
        env0.assert_expr_is_of_type(exb, T_String)
        return (T_String, env0)

    @exprd.put(r"{EX} : an implementation-defined timezone name")
    def _(expr, env0, _):
        [] = expr.children
        return (T_String, env0)

    @exprd.put(r"{EX} : the escape sequence for {var} as specified in the “Escape Sequence” column of the corresponding row")
    def _(expr, env0, _):
        [var] = expr.children
        return (T_String, env0)

    # ----------------------------------------------------------
    # return T_character_

    @exprd.put(r"{EXPR} : the character matched by {PROD_REF}")
    def _(expr, env0, _):
        [prod_ref] = expr.children
        return (T_character_, env0)

    @exprd.put(r"{EXPR} : the character whose character value is {var}")
    def _(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_MathInteger_)
        return (T_character_, env1)

    @exprd.put(r'{EXPR} : the result of applying that mapping to {var}')
    def _(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_character_)
        return (T_character_, env1)

    @exprd.put(r'{EXPR} : the one character in CharSet {var}')
    def _(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_CharSet)
        return (T_character_, env1)

    @exprd.put(r"{EXPR} : the character {SETTABLE}")
    def _(expr, env0, _):
        [settable] = expr.children
        env1 = env0.ensure_expr_is_of_type(settable, T_character_)
        return (T_character_, env1)

    # ----------------------------------------------------------
    # return T_code_unit_

    @exprd.put(r'{code_unit_lit} : \b 0x [0-9A-F]{4} \x20 \( [A-Z -]+ \)')
    @exprd.put(r'{code_unit_lit} : the \x20 code \x20 unit \x20 0x [0-9A-F]{4} \x20 \( [A-Z -]+ \)')
    def _(expr, env0, _):
        return (T_code_unit_, env0)

    @exprd.put(r"{EX} : the code unit whose value is determined by {PROD_REF} according to {h_emu_xref}")
    def _(expr, env0, _):
        [nonterminal, emu_xref] = expr.children
        return (T_code_unit_, env0)

    @exprd.put(r"{EX} : the code unit whose value is {EX}")
    def _(expr, env0, _):
        [ex] = expr.children
        env1 = env0.ensure_expr_is_of_type(ex, T_MathInteger_ | T_MathInteger_)
        return (T_code_unit_, env0)

    @exprd.put(r"{EXPR} : the code unit whose numeric value is that of {EXPR}")
    def _(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_code_point_)
        return (T_code_unit_, env0)

    @exprd.put(r"{EXPR} : the code unit whose numeric value is {EX}")
    def _(expr, env0, _):
        [ex] = expr.children
        env0.assert_expr_is_of_type(ex, T_MathNonNegativeInteger_)
        return (T_code_unit_, env0)
    # return T_code_point_

    @exprd.put(r"{EXPR} : the code point {var}")
        # This means "the code point whose numeric value is {var}"
    @exprd.put(r"{EXPR} : the code point whose numeric value is {NAMED_OPERATION_INVOCATION}")
    def _(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_MathInteger_)
        return (T_code_point_, env0)

    @exprd.put(r"{EXPR} : the code point whose numeric value is that of {var}")
    def _(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_code_unit_)
        return (T_code_point_, env0)

    @exprd.put(r'{code_point_lit} : ` [^`]+ ` \x20 U \+ [0-9A-F]{4} \x20 \( [A-Z -]+ \)')
    @exprd.put(r'{code_point_lit} : \b U \+ [0-9A-F]{4} \x20 \( [A-Z -]+ \)')
    def _(expr, env0, _):
        return (T_code_point_, env0)

    # ----------------------------------------------------------
    # return T_Unicode_code_points_

    @exprd.put(r"{EXPR} : the result of toLowercase({var}), according to the Unicode Default Case Conversion algorithm")
    def _(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_Unicode_code_points_)
        return (T_Unicode_code_points_, env0)

    @exprd.put(r"{EXPR} : the result of toUppercase(« {var} »), according to the Unicode Default Case Conversion algorithm")
    def _(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_code_point_)
        return (T_Unicode_code_points_, env0)

    # ----------------------------------------------------------
    # return ListType

    # --------------------
    # ListType(T_MathInteger_)

    @exprd.put(r"{EXPR} : a List of length {var} whose elements are nondeterministically chosen byte values")
    def _(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_MathInteger_)
        return (ListType(T_MathInteger_), env0)

    @exprd.put(r"{EXPR} : the List of octets resulting by applying the UTF-8 transformation to {DOTTING}")
    def _(expr, env0, _):
        [dotting] = expr.children
        env1 = env0.ensure_expr_is_of_type(dotting, T_code_point_)
        return (ListType(T_MathInteger_), env1)

    # ---------------
    # ListType(other)

    @exprd.put(r"{EXPR} : the List of arguments that was passed to this function by {dsb_word} or {dsb_word}")
    def _(expr, env0, _):
        [dsbwa, dsbwb] = expr.children
        assert dsbwa.source_text() == '[[Call]]'
        assert dsbwb.source_text() == '[[Construct]]'
        return (ListType(T_Tangible_), env0)

    @exprd.put(r"{EXPR} : {var}<sup>th</sup> element of {var}'s _captures_ List")
    def _(expr, env0, _):
        [n_var, state_var] = expr.children
        env0.assert_expr_is_of_type(n_var, T_MathInteger_)
        env0.assert_expr_is_of_type(state_var, T_MatchState)
        return (T_captures_entry_, env0)

    @exprd.put(r"{EX} : {var}'s _input_")
    def _(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_MatchState)
        return (ListType(T_character_), env1)

    # --------------------------------------------------------
    # return T_Parse_Node

    @exprd.put(r"{EXPR} : the Parse Node (an instance of {var}) at the root of the parse tree resulting from the parse")
    def _(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_grammar_symbol_)
        return (T_Parse_Node, env0)

    # -------------------------------------------------
    # return T_CharSet

    @exprd.put(r'{EXPR} : the CharSet containing all characters with a character value greater than or equal to {var} and less than or equal to {var}')
    def _(expr, env0, _):
        [var1, var2] = expr.children
        env1 = env0.ensure_expr_is_of_type(var1, T_MathInteger_)
        env2 = env0.ensure_expr_is_of_type(var2, T_MathInteger_)
        assert env1 is env0
        assert env2 is env0
        return (T_CharSet, env0)

    @exprd.put(r"{EXPR} : the CharSet containing the single character {code_point_lit}")
    @exprd.put(r"{EXPR} : the CharSet containing the single character {var}")
    def _(expr, env0, _):
        [ex] = expr.children
        env0.ensure_expr_is_of_type(ex, T_character_)
        return (T_CharSet, env0)

    @exprd.put(r"{EXPR} : the CharSet containing the character matched by {PROD_REF}")
    def _(expr, env0, _):
        [prod_ref] = expr.children
        return (T_CharSet, env0)

    @exprd.put(r"{EXPR} : a one-element CharSet containing the character {var}")
    def _(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_character_)
        return (T_CharSet, env0)

    @exprd.put(r"{EXPR} : the union of CharSets {var}, {var} and {var}")
    def _(expr, env0, _):
        [va, vb, vc] = expr.children
        enva = env0.ensure_expr_is_of_type(va, T_CharSet)
        envb = env0.ensure_expr_is_of_type(vb, T_CharSet)
        envc = env0.ensure_expr_is_of_type(vc, T_CharSet)
        return (T_CharSet, envs_or([enva, envb, envc]))

    @exprd.put(r"{EXPR} : the union of {var} and {var}")
    @exprd.put(r"{EXPR} : the union of CharSets {var} and {var}")
    def _(expr, env0, _):
        [va, vb] = expr.children
        enva = env0.ensure_expr_is_of_type(va, T_CharSet)
        envb = env0.ensure_expr_is_of_type(vb, T_CharSet)
        return (T_CharSet, env_or(enva, envb))

    @exprd.put(r"{EXPR} : the CharSet of all characters")
    def _(expr, env0, _):
        [] = expr.children
        return (T_CharSet, env0)

    @exprd.put(r"{EXPR} : the ten-element CharSet containing the characters `0`, `1`, `2`, `3`, `4`, `5`, `6`, `7`, `8`, and `9`")
    def _(expr, env0, _):
        [] = expr.children
        return (T_CharSet, env0)

    @exprd.put(r"{EXPR} : the CharSet containing every character in {STR_LITERAL}")
    def _(expr, env0, _):
        [strlit] = expr.children
        return (T_CharSet, env0)

    @exprd.put(r"{EXPR} : the CharSet containing all characters not in {NAMED_OPERATION_INVOCATION}")
    def _(expr, env0, _):
        [noi] = expr.children
        env0.assert_expr_is_of_type(noi, T_CharSet)
        return (T_CharSet, env0)

    @exprd.put(r"{EXPR} : the CharSet containing all characters corresponding to a code point on the right-hand side of the {nonterminal} or {nonterminal} productions")
    def _(expr, env0, _):
        [nont1, nont2] = expr.children
        return (T_CharSet, env0)

    @exprd.put(r"{EXPR} : the empty CharSet")
    def _(expr, env0, _):
        [] = expr.children
        return (T_CharSet, env0)

    @exprd.put(r"{EXPR} : the CharSet containing all Unicode code points whose character database definition includes the property {var} with value {var}")
    def _(expr, env0, _):
        [va, vb] = expr.children
        env0.assert_expr_is_of_type(va, ListType(T_code_point_))
        env0.assert_expr_is_of_type(vb, ListType(T_code_point_))
        return (T_CharSet, env0)

    @exprd.put(r"{EXPR} : the CharSet containing all Unicode code points whose character database definition includes the property “General_Category” with value {var}")
    def _(expr, env0, _):
        [v] = expr.children
        env0.assert_expr_is_of_type(v, ListType(T_code_point_))
        return (T_CharSet, env0)

    @exprd.put(r"{EXPR} : the CharSet containing all Unicode code points whose character database definition includes the property {var} with value “True”")
    def _(expr, env0, _):
        [v] = expr.children
        env0.assert_expr_is_of_type(v, ListType(T_code_point_))
        return (T_CharSet, env0)

    @exprd.put(r"{EXPR} : the CharSet containing all Unicode code points included in {NAMED_OPERATION_INVOCATION}")
    @exprd.put(r"{EXPR} : the CharSet containing all Unicode code points not included in {NAMED_OPERATION_INVOCATION}")
    def _(expr, env0, _):
        [noi] = expr.children
        env0.assert_expr_is_of_type(noi, T_CharSet)
        return (T_CharSet, env0)

    @exprd.put(r"{EXPR} : the CharSet containing all characters {var} such that {var} is not in {var} but {NAMED_OPERATION_INVOCATION} is in {var}")
    def _(expr, env0, _):
        [loop_var, loop_var2, cs_var, noi, cs_var2] = expr.children
        assert loop_var.source_text() == loop_var2.source_text()
        assert cs_var.source_text() == cs_var2.source_text()
        env0.assert_expr_is_of_type(cs_var, T_CharSet)
        env1 = env0.plus_new_entry(loop_var, T_character_)
        env1.assert_expr_is_of_type(noi, T_character_)
        return (T_CharSet, env0)

    @exprd.put(r"{NAMED_OPERATION_INVOCATION} : the CharSet returned by {h_emu_grammar}")
    def _(expr, env0, _):
        [emu_grammar] = expr.children
        return (T_CharSet, env0)

    # ------------------------------------------------
    # return T_alg_steps

    @exprd.put(r"{EXPR} : the algorithm steps defined in {h_emu_xref}")
    def _(expr, env0, _):
        [emu_xref] = expr.children
        return (T_alg_steps, env0)

    # -------------------------------------------------
    # return proc type

    @exprd.put(r'{EXPR} : the abstract operation named in the Conversion Operation column in {h_emu_xref} for Element Type {var}')
    def _(expr, env0, _):
        [emu_xref, var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_TypedArray_element_type)
        return (ProcType([T_Tangible_], T_IntegralNumber_), env1)

    # -------------------------------------------------
    # whatever

    @exprd.put(r"{EXPR} : a copy of {var}'s _captures_ List")
    def _(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_MatchState)
        return (T_captures_list_, env1)

    @exprd.put(r"{EXPR} : the MatchState ({var}, {EX}, {var})")
    def _(expr, env0, _):
        [input_var, ex, var] = expr.children
        env0.assert_expr_is_of_type(input_var, ListType(T_character_))
        env1 = env0.ensure_expr_is_of_type(ex, T_MathInteger_); assert env1 is env0
        env2 = env0.ensure_expr_is_of_type(var, T_captures_list_); assert env2 is env0
        return (T_MatchState, env0)

    @exprd.put(r"{EXPR} : {var}'s MatchState")
    def _(expr, env0, _):
        # todo?: change to Assert: _r_ is a MatchState
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_MatchState)
        return (T_MatchState, env0)

    @exprd.put(r"{EXPR} : {var}'s _captures_ List")
    def _(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_MatchState)
        return (T_captures_list_, env1)

    @exprd.put(r"{SETTABLE} : the {DSBN} internal slot of this Date object")
    def _(expr, env0, _):
        [dsbn] = expr.children
        dsbn_name = dsbn.source_text()[2:-2]
        assert dsbn_name == 'DateValue'
        return (T_Number, env0)

    @exprd.put(r"{EX} : a newly created {ERROR_TYPE} object")
    def _(expr, env0, _):
        [error_type] = expr.children
        return (type_for_ERROR_TYPE(error_type), env0)

    @exprd.put(r"{EXPR} : the canonical {h_emu_not_ref_property_name} of {var} as given in the “Canonical {h_emu_not_ref_property_name}” column of the corresponding row")
    def _(expr, env0, _):
        [_, v, _] = expr.children
        env0.assert_expr_is_of_type(v, ListType(T_code_point_))
        return (ListType(T_code_point_), env0)

    @exprd.put(r"{EXPR} : the List of Unicode code points {var}")
    def _(expr, env0, _):
        [v] = expr.children
        env0.assert_expr_is_of_type(v, ListType(T_code_point_))
        return (ListType(T_code_point_), env0)

    @exprd.put(r"{EXPR} : the canonical property value of {var} as given in the “Canonical property value” column of the corresponding row")
    def _(expr, env0, _):
        [v] = expr.children
        env0.assert_expr_is_of_type(v, ListType(T_code_point_))
        return (ListType(T_code_point_), env0)

    # ----

    @exprd.put(r"{EXPR} : the WaiterList that is referenced by the pair ({var}, {var})")
    def _(expr, env0, _):
        [sdb, i] = expr.children
        env0.assert_expr_is_of_type(sdb, T_Shared_Data_Block)
        env0.assert_expr_is_of_type(i, T_MathInteger_)
        return (T_WaiterList, env0)

    @exprd.put(r"{EXPR} : a reference to the list of waiters in {var}")
    def _(expr, env0, _):
        [wl] = expr.children
        env0.assert_expr_is_of_type(wl, T_WaiterList)
        return (ListType(T_agent_signifier_), env0)

    @exprd.put(r"{EXPR} : this Date object")
    def _(expr, env0, _):
        [] = expr.children
        return (T_Object | ThrowType(T_TypeError), env0)

    @exprd.put(r"{EX} : the GlobalSymbolRegistry List")
    @exprd.put(r"{EX} : the GlobalSymbolRegistry List (see {h_emu_xref})")
    def _(expr, env0, _):
        return (ListType(T_GlobalSymbolRegistry_Record), env0)

    @exprd.put(r"{EX} : {backticked_word}")
    def _(expr, env0, _):
        [backticked_word] = expr.children
        word = backticked_word.source_text()[1:-1]
        if word == 'General_Category':
            return (T_Unicode_code_points_, env0)
        else:
            assert 0, word

    @exprd.put(r"{EXPR} : the intrinsic object listed in column one of {h_emu_xref} for {DOTTING}")
    def _(expr, env0, _):
        [emu_xref, dotting] = expr.children
        env0.assert_expr_is_of_type(dotting, T_String)
        return (T_function_object_, env0)

    @exprd.put('''{EXPR} : a String in the form of a {nonterminal} ({nonterminal} if {var} contains *"u"*) equivalent to {var} interpreted as UTF-16 encoded Unicode code points ({h_emu_xref}), in which certain code points are escaped as described below. {var} may or may not be identical to {var}; however, the Abstract Closure that would result from evaluating {var} as a {nonterminal} ({nonterminal} if {var} contains *"u"*) must behave identically to the Abstract Closure given by the constructed object's {DSBN} internal slot. Multiple calls to this abstract operation using the same values for {var} and {var} must produce identical results''')
    def _(expr, env0, _):
        # XXX
        return (T_String, env0)

    @exprd.put(r"{EXPR} : the time value (UTC) identifying the current time")
    def _(expr, env0, _):
        [] = expr.children
        return (T_IntegralNumber_, env0)

    @exprd.put(r"{EXPR} : the result of parsing {var} as a date, in exactly the same manner as for the `parse` method ({h_emu_xref})")
    def _(expr, env0, _):
        [var, emu_xref] = expr.children
        env0.assert_expr_is_of_type(var, T_String)
        return (T_Number, env0)

    @exprd.put(r"{EXPR} : the String value of the Constructor Name value specified in {h_emu_xref} for this <var>TypedArray</var> constructor")
    def _(expr, env0, _):
        [emu_xref] = expr.children
        return (T_String, env0)

    @exprd.put(r"{EXPR} : the Agent Events Record in {DOTTING} whose {DSBN} is {PP_NAMED_OPERATION_INVOCATION}")
    def _(expr, env0, _):
        [dotting, dsbn, e] = expr.children
        env0.assert_expr_is_of_type(dotting, ListType(T_Agent_Events_Record))
        assert dsbn.source_text() == '[[AgentSignifier]]'
        env0.assert_expr_is_of_type(e, T_agent_signifier_)
        return (T_Agent_Events_Record, env0)

    @exprd.put("{EXPR} : an implementation-defined String source code representation of {var}. The representation must have the syntax of a {nonterminal}. Additionally, if {var} has an {DSBN} internal slot and {DOTTING} is a String, the portion of the returned String that would be matched by {nonterminal} {nonterminal} must be the value of {DOTTING}")
    def _(expr, env0, _):
        var = expr.children[0]
        env0.assert_expr_is_of_type(var, T_function_object_)
        return (T_String, env0)

    @exprd.put(r"{EXPR} : an implementation-defined String source code representation of {var}. The representation must have the syntax of a {nonterminal}")
    def _(expr, env0, _):
        [var, nont] = expr.children
        env0.assert_expr_is_of_type(var, T_function_object_)
        return (T_String, env0)

    @exprd.put(r"{EX} : {backticked_oth}")
    def _(expr, env0, _):
        [_] = expr.children
        return (T_Unicode_code_points_, env0)

    @exprd.put(r"{EX} : the CaptureRange {PAIR}")
    def _(expr, env0, _):
        [pair] = expr.children
        # XXX
        return (T_CaptureRange, env0)

    @exprd.put(r"{EXPR} : a new Synchronize event")
    def _(expr, env0, _):
        [] = expr.children
        return (T_Synchronize_event, env0)

    @exprd.put(r"{SETTABLE} : the Synchronize event in {var}")
    def _(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_WaiterList)
        return (T_Synchronize_event, env0)

    # for PR #1961 compound_assignment
    @exprd.put(r"{MULTILINE_EXPR} : the {TABLE_RESULT_TYPE} associated with {var} in the following table:{_indent_}{nlai}{h_figure}{_outdent_}")
    def _(expr, env0, _):
        [table_result_type, var, h_figure] = expr.children
        table_result_type_str = table_result_type.source_text()
        if table_result_type_str == 'sequence of Unicode code points':
            result_type = T_Unicode_code_points_
        else:
            assert 0, table_result_type_str
        return (result_type, env0)

    @exprd.put(r"{MULTILINE_EXPR} : the {TABLE_RESULT_TYPE} associated with {var} and Type({var}) in the following table:{_indent_}{nlai}{h_figure}{_outdent_}")
    def _(expr, env0, _):
        [table_result_type, vara, varb, h_figure] = expr.children
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

    @exprd.put(r"{EX} : a nondeterministically chosen byte value")
    def _(expr, env0, _):
        [] = expr.children
        return (T_MathNonNegativeInteger_, env0)

    @exprd.put(r"{EXPR} : a List of one or more {ERROR_TYPE} objects representing the parsing errors and/or early errors. If more than one parsing error or early error is present, the number and ordering of error objects in the list is implementation-defined, but at least one must be present")
    def _(expr, env0, _):
        [error_type] = expr.children
        return (ListType(type_for_ERROR_TYPE(error_type)), env0)

    @exprd.put(r"{EXPR} : the empty sequence of Unicode code points")
    def _(expr, env0, _):
        [] = expr.children
        return (T_Unicode_code_points_, env0)

    @exprd.put(r"{EXPR} : a List whose elements are the elements of {var}, in the order in which they had their {dsb_word} fields set to {LITERAL} in {cap_word}")
    def _(expr, env0, _):
        [var, dsb_word, literal, cap_word] = expr.children
        assert dsb_word.source_text() == '[[AsyncEvaluation]]'
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_Cyclic_Module_Record))
        return (ListType(T_Cyclic_Module_Record), env1)

    @exprd.put(r"{RHSS} : {RHSS}{RHS}")
    def _(expr, env0, _):
        [rhss, rhs] = expr.children
        (t1, env1) = tc_expr(rhss, env0)
        (t2, env2) = tc_expr(rhs, env1)
        return (t1 | t2, env2)

    @exprd.put(r"{RHS} : {nlai}= {EXPR} if {CONDITION}")
    def _(expr, env0, _):
        [subexpr, cond] = expr.children
        (t_env, f_env) = tc_cond(cond, env0)
        (t, env1) = tc_expr(subexpr, t_env)
        return (t, env1)

    @exprd.put(r"{EX} : the largest integral Number &lt; {var} for which {CONDITION_1} (i.e., {var} represents the last local time before the transition)")
    def _(expr, env0, _):
        [vara, cond, varb] = expr.children
        # (t_env, f_env) = tc_cond(cond, env0)
        # refers to _possibleInstantsBefore_ which hasn't been defined yet, it's complicated
        return (T_IntegralNumber_, env0)

    @exprd.put(r"{EXPR} : that Record")
    def _(expr, env0, _):
        # InnerModuleLoading
        [] = expr.children
        return (T_LoadedModule_Record_, env0)

    @exprd.put(r"{EXPR} : an implementation-defined non-negative mathematical value")
    def _(expr, env0, _):
        [] = expr.children
        return (T_MathReal_, env0)

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
        'either ~return~ or ~throw~': T_return_ | T_throw_,
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
    # Initialize this dict with info for unnamed record types.
    # Then add info for named record types
    # by calling process_declared_record_type_info().

    #? # 2651: Table 8: Completion Record Fields
    #? 'Completion Record': {
    #?     'Type'   : T_completion_kind_,
    #?     'Value'  : T_Tangible_ | T_tilde_empty_,
    #?     'Target' : T_String | T_tilde_empty_,
    #? },

    'LoadedModule_Record_': {
        'Specifier' : T_String,
        'Module'    : T_Module_Record,
    },

    # 8.2: NO TABLE
    'templateMap_entry_': {
        'Site'    : T_Parse_Node,
        'Array'   : T_Object,
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

    'other Module Record': {
        'Realm'           : T_Realm_Record,
        'Environment'     : T_Module_Environment_Record | T_tilde_empty_,
        'Namespace'       : T_Object | T_tilde_empty_,
        'HostDefined'     : T_host_defined_,
    },

    # 24003
    'ExportResolveSet_Record_': {
        'Module'     : T_Module_Record,
        'ExportName' : T_String,
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

    # 25.2.3.2 FinalizationRegistry.prototype.register
    'FinalizationRegistryCellRecord_': {
        'WeakRefTarget'  : T_Object | T_tilde_empty_,
        'HeldValue'      : T_Tangible_,
        'UnregisterToken': T_Object | T_tilde_empty_,
    },

    # 39099: no table, no mention
    'MapData_record_': {
        'Key'   : T_Tangible_ | T_tilde_empty_,
        'Value' : T_Tangible_ | T_tilde_empty_,
        # but Value is empty only if Key is empty?
        # So if you establish that _e_.[[Key]] isn't ~empty~,
        # you know that _e_.[[Value]] isn't ~empty~ ?
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
        'Order'       : T_tilde_SeqCst_ | T_tilde_Unordered_ | T_tilde_Init_,
        'NoTear'      : T_Boolean,
        'Block'       : T_Shared_Data_Block,
        'ByteIndex'   : T_MathInteger_,
        'ElementSize' : T_MathInteger_,
    },

}

def process_declared_record_type_info():
    for record_schema in spec.RecordSchema_for_name_.values():

        d_from_spec = {}
        schemas = reversed([* record_schema.self_and_supers() ])
        for schema in schemas:
            for field_decl in schema.addl_field_decls.values():
                mo = re.fullmatch(r'\[\[(\w+)\]\]', field_decl.name)
                debracketed_field_name = mo.group(1) # backwards compat
                if field_decl.value_description is None:
                    t = convert_nature_to_type(field_decl.nature)
                else:
                    t = convert_nature_node_to_type(field_decl.value_description)

                key = (record_schema.tc_schema_name, debracketed_field_name)
                tweak = {
                    # See PR #2963:
                    ('Function Environment Record', 'FunctionObject'): ( T_Object           , T_function_object_ ),
                    ('Script Record'              , 'ECMAScriptCode'): ( T_Parse_Node       , T_PTN_Script ), 
                    ('Source Text Module Record'  , 'Context'       ): ( T_execution_context, T_execution_context | T_tilde_empty_ ),
                    ('Source Text Module Record'  , 'ImportMeta'    ): ( T_Object           , T_Object | T_tilde_empty_ ),
                    ('PromiseCapability Record'   , 'Promise'       ): ( T_Object           , T_Object | T_Undefined ),
                    ('PromiseCapability Record'   , 'Resolve'       ): ( T_function_object_ , T_function_object_ | T_Undefined ),
                    ('PromiseCapability Record'   , 'Reject'        ): ( T_function_object_ , T_function_object_ | T_Undefined ),

                    # --------------
                    # Just me?
                    ('AsyncGeneratorRequest Record', 'Completion' ): ( T_Abrupt | T_Normal, T_Tangible_ | T_return_ | T_throw_ | T_tilde_empty_ ),
                    ('JobCallback Record'          , 'HostDefined'): ( T_host_defined_    , T_host_defined_ | T_tilde_empty_ ),
                }.get(key, None)
                if tweak:
                    (t_from_spec, t_for_compat) = tweak
                    assert t == t_from_spec
                    t = t_for_compat

                d_from_spec[debracketed_field_name] = t

        if record_schema.tc_schema_name == 'Completion Record': continue

        ffrtn_name = record_schema.tc_schema_name
        # map from the title-case schema name in spec.RecordSchema_for_name_
        # to the name that the spec uses in practice (e.g., in {VAL_DESC}).
        ffrtn_name = re.sub(' Event$', ' event', ffrtn_name)
        ffrtn_name = re.sub('Candidate Execution Record', 'candidate execution', ffrtn_name)

        assert ffrtn_name not in fields_for_record_type_named_
        fields_for_record_type_named_[ffrtn_name] = d_from_spec

    # ----------------

    global record_type_with_fields_
    record_type_with_fields_ = defaultdict(list)
    for (record_type_name, fields_info) in fields_for_record_type_named_.items():
        field_names_str = ', '.join(sorted(fields_info.keys()))
        record_type_with_fields_[field_names_str].append(record_type_name)

def find_record_types_with_fields(field_names):
    field_names_str = ', '.join(sorted(field_names))
    return record_type_with_fields_[field_names_str]

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

type_of_internal_thing_ = {}

def set_up_internal_thing(method_or_slot, debracketed_name, stype):
    # Ignore `method_or_slot`
    if debracketed_name in type_of_internal_thing_:
        # [[GeneratorBrand]] is declared for both
        # Generator Instances and AsyncGenerator Instances.
        assert debracketed_name == 'GeneratorBrand', debracketed_name

        t = type_of_internal_thing_[debracketed_name]
        assert t == stype
    else:
        type_of_internal_thing_[debracketed_name] = stype

# 20.3 Boolean Objects
set_up_internal_thing('slot', 'BooleanData', T_Boolean)

# 20.4 Symbol Objects
set_up_internal_thing('slot', 'SymbolData', T_Symbol)

# 21.1 Number Objects
set_up_internal_thing('slot', 'NumberData', T_Number)

# 21.2 BigInt Objects
set_up_internal_thing('slot', 'BigIntData', T_BigInt)

# 21.4 Date Objects
set_up_internal_thing('slot', 'DateValue', T_IntegralNumber_ | T_NaN_Number_)

# 22.1 String Objects
set_up_internal_thing('slot', 'StringData', T_String)

# 22.2 RegExp (Regular Expression) Objects
set_up_internal_thing('slot', 'RegExpMatcher',  T_RegExpMatcher_)
set_up_internal_thing('slot', 'OriginalSource', T_String)
set_up_internal_thing('slot', 'OriginalFlags',  T_String)
set_up_internal_thing('slot', 'RegExpRecord',   T_RegExp_Record)

# 24.1 Map Objects
set_up_internal_thing('slot', 'MapData', ListType(T_MapData_record_))

# 24.2 Set Objects
set_up_internal_thing('slot', 'SetData', ListType(T_Tangible_ | T_tilde_empty_))

# 24.3 WeakMap Objects
set_up_internal_thing('slot', 'WeakMapData', ListType(T_MapData_record_))

# 24.4 WeakSet Objects
set_up_internal_thing('slot', 'WeakSetData', ListType(T_Tangible_ | T_tilde_empty_))

# 25.1 ArrayBuffer Objects
# 25.2 SharedArrayBuffer Objects
set_up_internal_thing('slot', 'ArrayBufferData',       T_Data_Block | T_Shared_Data_Block | T_Null)
    # XXX but IsSharedArrayBuffer() ensures that ArrayBufferData is a Shared Data Block
set_up_internal_thing('slot', 'ArrayBufferByteLength', T_MathInteger_)
set_up_internal_thing('slot', 'ArrayBufferDetachKey',  T_host_defined_)

# 26.1 WeakRef Objects
set_up_internal_thing('slot', 'WeakRefTarget', T_Object)

# 26.2 FinalizationRegistry Objects
set_up_internal_thing('slot', 'CleanupCallback', T_JobCallback_Record)
set_up_internal_thing('slot', 'Cells',           ListType(T_FinalizationRegistryCellRecord_))

# 27.2.1.3 CreatResolvingFunctions
set_up_internal_thing('slot', 'Promise',         T_Object)
set_up_internal_thing('slot', 'AlreadyResolved', T_boolean_value_record_)

# 27.2.4 Properties of the Promise Constructor
set_up_internal_thing('slot', 'AlreadyCalled',     T_boolean_value_record_ | T_Boolean)
set_up_internal_thing('slot', 'Index',             T_MathInteger_)
set_up_internal_thing('slot', 'Capability',        T_PromiseCapability_Record)
set_up_internal_thing('slot', 'RemainingElements', T_integer_value_record_)
set_up_internal_thing('slot', 'Values',            ListType(T_Tangible_))
set_up_internal_thing('slot', 'Errors',            ListType(T_Tangible_))

# 28.2.2.1 Proxy.revocable
set_up_internal_thing('slot', 'RevocableProxy', T_Proxy_exotic_object_ | T_Null)

# ------------------------------------------------------------------------------

def set_up_declared_internal_methods_and_slots():
    # Set up the internal methods and slots
    # that are declared in tables in the spec.
    for emu_table in spec.doc_node.each_descendant_named('emu-table'):
        if 'Internal' in emu_table._caption:
            if 'Internal Method' in emu_table._caption:
                method_or_slot = 'method'
            elif 'Internal Slot' in emu_table._caption:
                method_or_slot = 'slot'
            else:
                assert 0, emu_table._caption

            assert (method_or_slot, emu_table._header_row.cell_texts) in [
                ('method', ['Internal Method', 'Signature', 'Description']),
                ('slot',   ['Internal Slot',   'Type',      'Description']),
            ]

            for row in emu_table._data_rows:
                handle_internal_thing_declaration(method_or_slot, row)

def handle_internal_thing_declaration(method_or_slot, row):
    (thing_name, thing_nature, thing_desc) = row.cell_texts
    debracketed_thing_name = re.fullmatch('\[\[(\w+)\]\]', thing_name).group(1) # backwards compat

    if method_or_slot == 'method':

        # The 'declarations' for the essential internal methods
        # don't use the same "type" phrasing used everywhere else,
        # so we need an ad hoc conversion function:
        def internal_method_nature_to_type(nature):
            return {
                'Boolean'                        : T_Boolean,
                'Object'                         : T_Object,
                'Object | Null'                  : T_Object | T_Null,
                'Undefined | Property Descriptor': T_Undefined | T_Property_Descriptor,
                '_PropertyDescriptor_'           : T_Property_Descriptor,
                '_Receiver_'                     : T_Tangible_,
                '_propertyKey_'                  : T_String | T_Symbol,
                '_value_'                        : T_Tangible_,
                '<em>any</em>'                   : T_Tangible_,
                'a List of <em>any</em>'         : ListType(T_Tangible_),
                'List of property keys'          : ListType(T_String | T_Symbol),
            }[nature]

        (param_natures, return_nature) = re.fullmatch(r'\((.+)\) <b>\u2192</b> (.+)', thing_nature).groups()

        if param_natures == ' ':
            param_types = []
        else:
            param_types = [
                internal_method_nature_to_type(param_nature)
                for param_nature in param_natures.split(', ')
            ]

        return_type = internal_method_nature_to_type(return_nature)
        #> An internal method implicitly returns a Completion Record,
        #> either a normal completion that wraps
        #> a value of the return type shown in its invocation pattern,
        #> or a throw completion.
        return_type |= T_throw_

        t = ProcType(param_types, return_type)
        
    elif method_or_slot == 'slot':
        field_value_type = row.cell_nodes[1]._syntax_tree
        value_description = field_value_type.children[0]
        t = convert_nature_node_to_type(value_description)

        if debracketed_thing_name in ['PromiseFulfillReactions', 'PromiseRejectReactions']:
            assert row.cell_texts[1] == 'a List of PromiseReaction Records'
            assert t == ListType(T_PromiseReaction_Record)
            # But there are steps (in FulfillPromise and RejectPromise)
            # that explicitly set these slots to *undefined*.
            t |= T_Undefined
            # (Might be worth a PR.)

        # Module Namespace Exotic Object's [[Module]] slot:
        # it's declared as "a Module Record",
        # but should it be "a Cyclic Module Record"?

    else:
        assert 0, method_or_slot

    set_up_internal_thing(method_or_slot, debracketed_thing_name, t)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 4 Overview

# ==============================================================================
#@ 4.2 Hosts and Implementations

if 1:
    @condd.put(r"{CONDITION_1} : the host is a web browser")
    def _(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 5 Notational Conventions

#@ 5.1 Syntactic and Lexical Grammars

# ==============================================================================
#@ 5.1.1 Context-Free Grammars

#> A <em>context-free grammar</em> consists of a number of <em>productions</em>.
#> Each production has an abstract symbol called a <em>nonterminal</em>
#> as its <em>left-hand side</em>,
#> and a sequence of zero or more nonterminal and <em>terminal</em> symbols
#> as its <em>right-hand side</em>.
#> For each grammar, the terminal symbols are drawn from a specified alphabet.

if 1:
    # grammar symbol

    tbd['{VAL_DESC} : a grammar symbol'] = T_grammar_symbol_

    # -------------------
    # nonterminal symbols

    @exprd.put(r'{nonterminal} : \| [A-Za-z][A-Za-z0-9]* \?? (\[ .+? \])? \|')
    def _(expr, env0, _):
        nont_name = expr.source_text()[1:-1]
        # Note that |Foo| often denotes a Parse Node,
        # rather than a grammar symbol,
        # but we capture those cases before they can get to here.
        return (T_grammar_symbol_, env0)

    @exprd.put(r"{EXPR} : the grammar symbol {nonterminal}")
    def _(expr, env0, _):
        [nont] = expr.children
        return (T_grammar_symbol_, env0)

    @exprd.put(r"{G_SYM} : {nonterminal}")
    def _(expr, env0, _):
        return (T_grammar_symbol_, env0)

    @tbd.put('{VAL_DESC} : {nonterminal}')
    def _(val_desc, env):
        [nont] = val_desc.children
        return a_subset_of(T_grammar_symbol_)

    tbd['{VAL_DESC} : a nonterminal in one of the ECMAScript grammars'] = a_subset_of(T_grammar_symbol_)

    # ----------------
    # terminal symbols

    tbd['{VAL_DESC} : {backticked_word}'] = a_subset_of(T_grammar_symbol_)

    @exprd.put(r"{G_SYM} : {TERMINAL}")
    def _(expr, env0, _):
        return (T_grammar_symbol_, env0)

    @tbd.put('{VAL_DESC} : the {nonterminal} {TERMINAL}')
    def _(val_desc, env):
        [nont, term] = val_desc.children
        assert nont.source_text() == '|ReservedWord|'
        assert term.source_text() == "`super`"
        return a_subset_of(T_grammar_symbol_)

# ==============================================================================
#@ 5.1.4 The Syntactic Grammar

#> It defines a set of productions,
#> starting from two alternative goal symbols |Script| and |Module|, ...

if 1:
    @condd.put(r"{CONDITION_1} : the goal symbol of the syntactic grammar is {nonterminal}")
    def _(cond, env0, asserting):
        [nont] = cond.children
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : the syntactic goal symbol is not {nonterminal}")
    def _(cond, env0, asserting):
        [nont] = cond.children
        return (env0, env0)

#> When a parse is successful, it constructs a parse tree,
#> a rooted tree structure in which each node is a <dfn>Parse Node</dfn>.

if 1:
    tbd['{VAL_DESC} : a Parse Node'] = T_Parse_Node

    tbd['{LIST_ELEMENTS_DESCRIPTION} : Parse Nodes'] = T_Parse_Node

#> Each Parse Node is an <em>instance</em> of a symbol in the grammar;
#> it represents a span of the source text that can be derived from that symbol.

if 1:
    tbd['{VAL_DESC} : an instance of a nonterminal'] = a_subset_of(T_Parse_Node)

    @tbd.put('{VAL_DESC} : an instance of {var}')
    def _(val_desc, env):
        [var] = val_desc.children
        env.assert_expr_is_of_type(var, T_grammar_symbol_)
        return a_subset_of(T_Parse_Node)

    @tbd.put('{VAL_DESC} : an? {nonterminal}')
    @tbd.put('{VAL_DESC} : an? {nonterminal} Parse Node')
    def _(val_desc, env):
        [nonterminal] = val_desc.children

        if val_desc.source_text() == 'a |ReservedWord|':
            # In Early Errors for ExportDeclaration, there is the condition
            #     StringValue of _n_ is a |ReservedWord|
            # This isn't asking if StringValue of _n_ is a Parse Node
            # that is an instance of |ReservedWord|.
            # Rather, it's asking if it's a String that could be matched by |ReservedWord|.
            return a_subset_of(T_String)

        return ptn_type_for(nonterminal)

        # '_x_ is a {nonterminal}'
        # might also mean that _x_ is a Parse Node
        # that isn't itself an instance of {nonterminal},
        # but connects by unit derivations to one that is.

    @tbd.put('{LIST_ELEMENTS_DESCRIPTION} : {nonterminal} Parse Nodes')
    def _(led, env):
        [nonterminal] = led.children
        return ptn_type_for(nonterminal)

    @exprd.put(r'{EXPR} : the source text that was recognized as {PROD_REF}')
    def _(expr, env0, _):
        [nonterminal] = expr.children
        # XXX Should check whether nonterminal makes sense
        # with respect to the emu-grammar accompanying this alg/expr.
        return (T_Unicode_code_points_, env0)

    @exprd.put(r"{EXPR} : the source text matched by {PROD_REF}")
    def _(expr, env0, _):
        [nont] = expr.children
        return (T_Unicode_code_points_, env0) # XXX spec bug: needs to be T_String?

    @exprd.put(r"{EX} : the code point matched by {PROD_REF}")
    def _(expr, env0, _):
        [nont] = expr.children
        return (T_code_point_, env0)

    @exprd.put(r"{EX} : the single code point matched by this production")
    def _(expr, env0, _):
        [] = expr.children
        return (T_code_point_, env0)

    @exprd.put(r'{EX} : the number of code points in {PROD_REF}')
    def _(expr, env0, _):
        [prod_ref] = expr.children
        env0.assert_expr_is_of_type(prod_ref, T_Parse_Node)
        return (T_MathNonNegativeInteger_, env0)

    @exprd.put(r"{EX} : the number of code points in {PROD_REF}, excluding all occurrences of {nonterminal}")
    def _(expr, env0, _):
        [prod_ref, nont] = expr.children
        return (T_MathNonNegativeInteger_, env0)

    @condd.put(r"{CONDITION_1} : any source text is matched by this production")
    def _(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

    # 13.2.3.1
    @condd.put(r"{CONDITION_1} : {PROD_REF} is the token `false`")
    @condd.put(r"{CONDITION_1} : {PROD_REF} is the token `true`")
    def _(cond, env0, asserting):
        [prod_ref] = cond.children
        assert prod_ref.source_text() == '|BooleanLiteral|'
        return (env0, env0)

#> When a Parse Node is an instance of a nonterminal,
#> it is also an instance of some production
#> that has that nonterminal as its left-hand side.

if 1:
    tbd['{VAL_DESC} : an instance of a production in {h_emu_xref}'] = a_subset_of(T_Parse_Node)

    @tbd.put('{VAL_DESC} : an instance of the production {h_emu_grammar}')
    def _(val_desc, env):
        [emu_grammar] = val_desc.children
        emu_grammar_text = emu_grammar.source_text()
        lhs = re.sub(r'<emu-grammar>(\w+) :.*', r'\1', emu_grammar_text)
        prodn_type = ptn_type_for(lhs)
        return a_subset_of(prodn_type)

    @exprd.put(r"{EXPR} : an instance of the production {h_emu_grammar}")
    def _(expr, env0, _):
        [emu_grammar] = expr.children
        assert emu_grammar.source_text() == '<emu-grammar>FormalParameters : [empty]</emu-grammar>'
        return (ptn_type_for('FormalParameters'), env0)

    @condd.put(r"{CONDITION_1} : {LOCAL_REF} is {h_emu_grammar}")
    def _(cond, env0, asserting):
        [local_ref, h_emu_grammar] = cond.children
        env0.assert_expr_is_of_type(local_ref, T_Parse_Node)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {LOCAL_REF} is {h_emu_grammar}, {h_emu_grammar}, {h_emu_grammar}, {h_emu_grammar}, or {h_emu_grammar}")
    def _(cond, env0, asserting):
        [local_ref, *h_emu_grammar_] = cond.children
        env0.assert_expr_is_of_type(local_ref, T_Parse_Node)
        return (env0, env0)

    @condd.put(r'{CONDITION_1} : {PROD_REF} is `export` {nonterminal}')
    def _(cond, env0, asserting):
        [prod_ref, nont] = cond.children
        return (env0, env0)

#> Moreover, it has zero or more <em>children</em>,
#> one for each symbol on the production's right-hand side:
#> each child is a Parse Node that is an instance of the corresponding symbol.

if 1:
    @nv.put(r"{EACH_THING} : child node {var} of this Parse Node")
    def _(each_thing, env0):
        [loop_var] = each_thing.children
        env1 = env0.plus_new_entry(loop_var, T_Parse_Node)
        return env1

# (Each child of _P_ is 'nested' directly within _P_.)

if 1:
    @condd.put(r"{CONDITION_1} : {LOCAL_REF} is not nested, directly or indirectly (but not crossing function or `static` initialization block boundaries), within an {nonterminal}")
    def _(cond, env0, asserting):
        [local_ref, nont] = cond.children
        env0.assert_expr_is_of_type(local_ref, T_Parse_Node)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {LOCAL_REF} is not nested, directly or indirectly (but not crossing function or `static` initialization block boundaries), within an {nonterminal} or a {nonterminal}")
    def _(cond, env0, asserting):
        [local_ref, nonta, nontb] = cond.children
        env0.assert_expr_is_of_type(local_ref, T_Parse_Node)
        return (env0, env0)

# (_P_ 'contains' its children and their children, and so on)

    @condd.put(r"{CONDITION_1} : {var} contains a {nonterminal}")
    @condd.put(r"{CONDITION_1} : {var} contains an? {nonterminal} Parse Node")
    @condd.put(r"{CONDITION_1} : {var} does not contain an? {nonterminal} Parse Node")
    @condd.put(r"{CONDITION_1} : {var} does not contain two {nonterminal} Parse Nodes")
    def _(cond, env0, asserting):
        [var, nont] = cond.children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        env0.assert_expr_is_of_type(nont, T_grammar_symbol_)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {var} does not contain a rest parameter, any binding patterns, or any initializers. It may contain duplicate identifiers")
    def _(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        return (env0, env0)

    @nv.put(r"{EACH_THING} : {nonterminal} {var} that {var} contains")
    def _(each_thing, env0):
        [nont, loop_var, root_var] = each_thing.children
        env0.assert_expr_is_of_type(root_var, T_Parse_Node)
        return env0.plus_new_entry(loop_var, ptn_type_for(nont))

    @exprd.put(r"{EXPR} : the number of {h_emu_grammar} Parse Nodes contained within {var}")
    def _(expr, env0, _):
        [emu_grammar, root_var] = expr.children
        env0.assert_expr_is_of_type(root_var, T_Parse_Node)
        return (T_MathNonNegativeInteger_, env0)

    @exprd.put(r"{EXPR} : the number of {h_emu_grammar} Parse Nodes contained within {var} that either occur before {var} or contain {var}")
    def _(expr, env0, _):
        [emu_grammar, root_var, x_var, x_var2] = expr.children
        env0.assert_expr_is_of_type(root_var, T_Parse_Node)
        env0.assert_expr_is_of_type(x_var, T_Parse_Node)
        assert x_var.source_text() == x_var2.source_text()
        return (T_MathNonNegativeInteger_, env0)

    @condd.put(r"{CONDITION_1} : {LOCAL_REF} contains two or more {nonterminal}s for which {NAMED_OPERATION_INVOCATION} is the same")
    def _(cond, env0, asserting):
        [local_ref, nonta, noi] = cond.children
        env0.assert_expr_is_of_type(local_ref, T_Parse_Node)
        # XXX noi
        return (env0, env0)

# (You can ask about nodes that contain _P_)

    @exprd.put(r"{PROD_REF} : the {nonterminal} containing {LOCAL_REF}")
    def _(expr, env0, _):
        [nonta, local_ref] = expr.children
        return (T_Parse_Node, env0)

    @exprd.put(r"{EXPR} : the {nonterminal}, {nonterminal}, or {nonterminal} that most closely contains {var}")
    def _(expr, env0, _):
        [*nont_, var] = expr.children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        return (T_Parse_Node, env0)

    @condd.put(r"{CONDITION_1} : {var} is not contained within an? {nonterminal}, {nonterminal}, or {nonterminal}")
    def _(cond, env0, asserting):
        [var, *nont_] = cond.children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {PROD_REF} is contained within a {nonterminal} that is being parsed for JSON.parse (see step {h_emu_xref} of {h_emu_xref})")
    @condd.put(r"{CONDITION_1} : {PROD_REF} is contained within a {nonterminal} that is being evaluated for JSON.parse (see step {h_emu_xref} of {h_emu_xref})")
    def _(cond, env0, asserting):
        [prod_ref, nont, step_xref, alg_xref] = cond.children
        env0.assert_expr_is_of_type(prod_ref, T_Parse_Node)
        return (env0, env0)

#> Parse Nodes are considered <dfn>the same Parse Node</dfn>
#> if and only if they represent the same span of source text,
#> are instances of the same grammar symbol,
#> and resulted from the same parser invocation.

if 1:
    @condd.put(r"{CONDITION_1} : {EX} is the same Parse Node as {EX}")
    def _(cond, env0, asserting):
        [exa, exb] = cond.children
        env0.assert_expr_is_of_type(exa, T_Parse_Node)
        env0.assert_expr_is_of_type(exb, T_Parse_Node)
        return (env0, env0)

#> ... In such cases a more restrictive supplemental grammar is provided
#> that further restricts the acceptable token sequences.
#> Typically, an early error rule will then state that, in certain contexts,
#> "_P_ <dfn>must cover</dfn> an _N_",
#> where _P_ is a Parse Node (an instance of the generalized production)
#> and _N_ is a nonterminal from the supplemental grammar.
#> This means:
#>  -- The sequence of tokens originally matched by _P_
#>     is parsed again using _N_ as the goal symbol.
#>     If _N_ takes grammatical parameters, then they are set to
#>     the same values used when _P_ was originally parsed.
#>  -- If the sequence of tokens can be parsed as a single instance of _N_,
#>     with no tokens left over, then:
#>       -- We refer to that instance of _N_ (a Parse Node, unique for a given _P_)
#>          as "the _N_ that is <dfn>covered</dfn> by _P_".
#>       -- All Early Error rules for _N_ and its derived productions
#>          also apply to the _N_ that is covered by _P_.
#>  -- Otherwise (if the parse fails), it is an early Syntax Error.

if 1:
    @nv.put(r"{EE_RULE} : {LOCAL_REF} must cover an? {nonterminal}.")
    def _(anode, env0):
        [local_ref, nont] = anode.children
        env0.assert_expr_is_of_type(local_ref, T_Parse_Node)
        return None

    @exprd.put(r"{EXPR} : the {nonterminal} that is covered by {LOCAL_REF}")
    def _(expr, env0, _):
        [nonterminal, local_ref] = expr.children
        env0.assert_expr_is_of_type(local_ref, T_Parse_Node)
        return (ptn_type_for(nonterminal), env0)

# (this text would be matched by that nonterminal/production
# if it were source text in an appropriate context)

    @condd.put(r"{CONDITION_1} : {NAMED_OPERATION_INVOCATION} is not some Unicode code point matched by the {nonterminal} lexical grammar production")
    def _(cond, env0, asserting):
        [noi, nont] = cond.children
        env0.assert_expr_is_of_type(noi, T_code_point_)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {NAMED_OPERATION_INVOCATION} is not matched by the {nonterminal} lexical grammar production")
    def _(cond, env0, asserting):
        [noi, nont] = cond.children
        env0.assert_expr_is_of_type(noi, T_code_point_)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {NAMED_OPERATION_INVOCATION} is not the numeric value of some code point matched by the {nonterminal} lexical grammar production")
    def _(cond, env0, asserting):
        [noi, nont] = cond.children
        env0.assert_expr_is_of_type(noi, T_MathInteger_)
        return (env0, env0)

# ==============================================================================
#@ 5.1.5.4 Grammatical Parameters

if 1:
    @condd.put(r"{CONDITION_1} : {PROD_REF} has an? <sub>[{cap_word}]</sub> parameter")
    def _(cond, env0, asserting):
        [prod_ref, cap_word] = cond.children
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : the <sub>[Tagged]</sub> parameter was not set")
    def _(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

# ==============================================================================
#@ 5.2 Algorithm Conventions

if 1:
    @condd.put(r"{CONDITION_1} : control reaches here")
    def _(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

# ------------------------------------------------------------------------------
#> The specification often uses a numbered list to specify steps in an algorithm.
#> Algorithm steps may be subdivided into sequential substeps.
#> Substeps are indented
#> and may themselves be further divided into indented substeps.

if 1:
    @nv.put(r'{EMU_ALG_BODY} : {IND_COMMANDS}{nlai}')
    def _(anode, env0):
        [ind_commands] = anode.children
        env1 = tc_nonvalue(ind_commands, env0)
        if env1 is not None:
            # Control falls off the end of the algorithm.
            add_pass_error(
                ind_commands,
                "Control falls off the end of the algorithm (need an explicit Return?)"
            )
            default_return_value = T_not_returned # or T_tilde_unused_, see PR #2397
            proc_add_return(env1, default_return_value, ind_commands)
            return None
        else:
            # All control paths end with a 'Return'
            return None

    @nv.put(r'{COMMANDS} : {COMMANDS}{_NL_N} {COMMAND}')
    def _(anode, env0):
        [commands, command] = anode.children
        env1 = tc_nonvalue(commands, env0)
        env2 = tc_nonvalue(command, env1)
        return env2

# ------------------------------------------------------------------------------
#> A step or substep may be written as an “if” predicate that conditions its substeps.
#> In this case, the substeps are only applied if the predicate is true.
#> If a step or substep begins with the word “else”,
#> it is a predicate that is the negation of
#> the preceding “if” predicate step at the same level.

if 1:
    @nv.put(r'{IF_CLOSED} : If {CONDITION}, {SMALL_COMMAND}. Otherwise {SMALL_COMMAND}.')
    @nv.put(r'{IF_CLOSED} : If {CONDITION}, {SMALL_COMMAND}. Otherwise, {SMALL_COMMAND}.')
    @nv.put(r'{IF_CLOSED} : If {CONDITION}, {SMALL_COMMAND}; else {SMALL_COMMAND}.')
    @nv.put(r'{IF_CLOSED} : If {CONDITION}, {SMALL_COMMAND}; otherwise {SMALL_COMMAND}.')
    @nv.put(r'{IF_CLOSED} : If {CONDITION}, {SMALL_COMMAND}; otherwise, {SMALL_COMMAND}.')
    def _(anode, env0):
        [cond, t_command, f_command] = anode.children
        (t_env, f_env) = tc_cond(cond, env0)
        t_benv = tc_nonvalue(t_command, t_env)
        f_benv = tc_nonvalue(f_command, f_env)
        return env_or(t_benv, f_benv)

    @nv.put(r'{IF_CLOSED} : If {CONDITION}, {SMALL_COMMAND}; else if {CONDITION}, {SMALL_COMMAND}; else {SMALL_COMMAND}.')
    def _(anode, env0):
        [cond_a, command_a, cond_b, command_b, command_c] = anode.children
        (a_t_env, a_f_env) = tc_cond(cond_a, env0)
        a_benv = tc_nonvalue(command_a, a_t_env)
        (b_t_env, b_f_env) = tc_cond(cond_b, a_f_env)
        b_benv = tc_nonvalue(command_b, b_t_env)
        c_benv = tc_nonvalue(command_c, b_f_env)
        return envs_or([a_benv, b_benv, c_benv])

    @nv.put(r'{IF_OTHER} : {IF_OPEN}{IF_TAIL}')
    def _(anode, env0):
        [if_open, if_tail] = anode.children

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

        # kludges to detect no-fall-through when STA can't:

        if_open_st = if_open.source_text()

        if if_open_st == 'If |BooleanLiteral| is the token `true`, return *true*.':
            # This occurs once, in the Evaluation semantics for `Literal : BooleanLiteral`:
            #     1. If |BooleanLiteral| is the token `false`, return *false*.
            #     1. If |BooleanLiteral| is the token `true`, return *true*.
            # These two steps exhaust the possibilities for |BooleanLiteral|,
            # and each one results in a 'return',
            # so it's impossible for control to fall through the second one.
            # todo: change "If" to "Else"?
            result = None

        if if_open_st.startswith('If abs(\u211d(_base_)) &lt; 1, return'):
            # Twice, near the bottom of Number::exponentiate,
            # there are 3 steps of the form:
            #     1. If abs(R(_base_)) > 1, return ...
            #     1. If abs(R(_base_)) is 1, return ...
            #     1. If abs(R(_base_)) &lt; 1, return ...
            # These steps exhaust the possibilities for abs(R(_base_)),
            # and since each one does a return,
            # it's impossible for control to fall through the last one.
            result = None

        return result

    @nv.put(r"{ELSE_PART} : Else, {CONDITION_1}. {COMMAND}")
    def _(anode, env0):
        [cond, comm] = anode.children
        (t_env, f_env) = tc_cond(cond, env0, asserting=True)
        return tc_nonvalue(comm, t_env)

    # -------------------------------------------------

    @exprd.put(r"{EXPR} : {EX} if {CONDITION}. Otherwise, it is {EXPR}")
    def _(expr, env0, _):
        [exa, cond, exb] = expr.children
        (t_env, f_env) = tc_cond(cond, env0)
        (ta, enva) = tc_expr(exa, t_env)
        (tb, envb) = tc_expr(exb, f_env)
        return (ta | tb, env_or(enva, envb))

# ------------------------------------------------------------------------------
#> A step may specify the iterative application of its substeps.</p>

if 1:
    @nv.put(r'{COMMAND} : Repeat,{IND_COMMANDS}')
    def _(anode, env0):
        [commands] = anode.children

        env_at_bottom = tc_nonvalue(commands, env0)

        # The only way to leave a condition-less Repeat
        # is via a Return command,
        # so there can't be anything (except maybe a NOTE) after the loop.
        return None

        # XXX Should repeat the analysis, feeding the bottom env to the top,
        # XXX until no change.
        # XXX (and likewise with other loops)


    @nv.put(r'{COMMAND} : Repeat, while {CONDITION},{IND_COMMANDS}')
    @nv.put(r"{COMMAND} : Repeat, until {CONDITION},{IND_COMMANDS}")
    def _(anode, env0):
        [cond, commands] = anode.children
        (t_env, f_env) = tc_cond(cond, env0)

        p = str(anode.prod)
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
            result = result.plus_new_entry('_r_', T_MatchState)

        return result

    @nv.put(r"{COMMAND} : While {CONDITION}, an implementation may perform the following steps:{IND_COMMANDS}")
    def _(anode, env0):
        [cond, commands] = anode.children
        (t_env, f_env) = tc_cond(cond, env0)
        bottom_env = tc_nonvalue(commands, t_env)
        reduced_bottom_env = bottom_env.reduce(t_env.vars.keys())
        return f_env

    @nv.put(r'{COMMAND} : For each {EACH_THING}, do{IND_COMMANDS}')
    @nv.put(r'{COMMAND} : For each {EACH_THING}, {SMALL_COMMAND}.')
    def _(anode, env0):
        [each_thing, commands] = anode.children

        env_for_commands  = tc_nonvalue(each_thing, env0)

        env_after_commands = tc_nonvalue(commands, env_for_commands)
        # XXX do I need to feed this back somehow?

        # Assume the loop-var doesn't survive the loop
        # if loop_var:
        #     result = env_after_commands.with_var_removed(loop_var)
        # else:
        #     result = env_after_commands

        # The only variables that 'exit' the loop are those that existed beforehand.
        names = env0.vars.keys()
        return env_after_commands.reduce(names)

    @nv.put(r"{EACH_THING} : {ITEM_NATURE} {var} such that {CONDITION}")
    @nv.put(r"{EACH_THING} : {ITEM_NATURE} {var} such that {CONDITION}, in ascending order")
    @nv.put(r"{EACH_THING} : {ITEM_NATURE} {var} such that {CONDITION}, in descending order")
    def _(each_thing, env0):
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
        return tenv

    @nv.put("{EACH_THING} : {ITEM_NATURE} {var} of {EX}")
    @nv.put("{EACH_THING} : {ITEM_NATURE} {var} that is an element of {EX}")
    def _(each_thing, env0):
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
        return env1.plus_new_entry(loop_var, item_type)

    @condd.put(r"{CONDITION_1} : The following loop will terminate")
    def _(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

# ------------------------------------------------------------------------------
#> A step that begins with “<dfn>Assert</dfn>:”
#> asserts an invariant condition of its algorithm.

if 1:
    @nv.put(r'{COMMAND} : Assert: {CONDITION}.')
    def _(anode, env0):
        [condition] = anode.children
        (t_env, f_env) = tc_cond(condition, env0, asserting=True)
        # throw away f_env
        return t_env

    @nv.put(r"{COMMAND} : Assert: If {CONDITION}, then {CONDITION}.")
    @nv.put(r"{COMMAND} : Assert: If {CONDITION}, {CONDITION}.")
    def _(anode, env0):
        [cond1, cond2] = anode.children
        (t1_env, f1_env) = tc_cond(cond1, env0)
        (t2_env, f2_env) = tc_cond(cond2, t1_env, asserting=True)
        return env_or(f1_env, t2_env)

    @nv.put(r"{COMMAND} : Assert: {CONDITION_1} if and only if {CONDITION_1}.")
    def _(anode, env0):
        [cond1, cond2] = anode.children
        (t1_env, f1_env) = tc_cond(cond1, env0)
        (t2_env, f2_env) = tc_cond(cond2, env0)
        return env_or(
            env_and(t1_env, t2_env),
            env_and(f1_env, f2_env)
        )

    @nv.put(r"{COMMAND} : Assert: {CONDITION_1} if {CONDITION_1}; otherwise, {CONDITION_1}.")
    def _(anode, env0):
        [cond_t, cond_x, cond_f] = anode.children
        (xt_env, xf_env) = tc_cond(cond_x, env0)
        (tt_env, tf_env) = tc_cond(cond_t, xt_env, asserting=True)
        (ft_env, ff_env) = tc_cond(cond_f, xf_env, asserting=True)
        return env_or(tt_env, ft_env)

    @nv.put(r"{COMMAND} : Assert: {CONDITION_1}, since {CONDITION_1}.")
    def _(anode, env0):
        [conda, condb] = anode.children
        (ta_env, fa_env) = tc_cond(conda, env0, asserting=True)
        (tb_env, fb_env) = tc_cond(condb, env0, asserting=True)
        return env_and(ta_env, tb_env)

# ------------------------------------------------------------------------------
#> Algorithm steps may declare named aliases for any value
#> using the form “Let _x_ be _someValue_”.

if 1:
    @exprd.put(r'{var} : \b _ [A-Za-z][A-Za-z0-9]* _ \b')
    def _(expr, env0, _):
        [var_name] = expr.children
        return (env0.vars[var_name], env0)

    # Let {var} be ...

    @nv.put(r"{COMMAND} : Let {var} be {EXPR}. (It may be evaluated repeatedly.)")
    @nv.put(r"{COMMAND} : Let {var} be {EXPR}.")
    @nv.put(r"{COMMAND} : Let {var} be {MULTILINE_EXPR}")
    @nv.put(r"{SMALL_COMMAND} : let {var} be {EXPR}")
    @nv.put(r"{SMALL_COMMAND} : let {var} be {EXPR}, indicating that an ordinary object should be created as the global object")
    @nv.put(r"{SMALL_COMMAND} : let {var} be {EXPR}, indicating that {var}'s global `this` binding should be the global object")
    def _(anode, env0):
        [var, expr] = anode.children[0:2]
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
                return env1
            elif expr_t == T_TBD:
                return env1
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
                return env1
            elif expr_t.is_a_subtype_of_or_equal_to(var_t):
                add_pass_error(
                    anode,
                    "... also, this narrows the type of var from %s to %s" % (var_t, expr_t)
                )
                return env1.with_expr_type_narrowed(var, expr_t)
            else:
                add_pass_error(
                    anode,
                    "... also, this changes the type of var from %s to %s" % (var_t, expr_t)
                )
                return env1.with_expr_type_replaced(var, expr_t)
        else:
            # The normal case.
            return env1.plus_new_entry(var, expr_t)

    @nv.put(r"{COMMAND} : Let {var} be {EXPR}. (However, if {var} is 10 and {var} contains more than 20 significant digits, every significant digit after the 20th may be replaced by a 0 digit, at the option of the implementation; and if {var} is not 2, 4, 8, 10, 16, or 32, then {var} may be an implementation-approximated integer representing the integer value denoted by {var} in radix-{var} notation.)")
    def _(anode, env0):
        [let_var, expr, rvar, zvar, rvar2, let_var2, zvar2, rvar3] = anode.children
        assert same_source_text(let_var, let_var2)
        assert same_source_text(rvar, rvar2)
        assert same_source_text(rvar, rvar3)
        assert same_source_text(zvar, zvar2)
        (t, env1) = tc_expr(expr, env0)
        return env1.plus_new_entry(let_var, t)

    @nv.put(r"{COMMAND} : Let {var} be an integer for which {NUM_EXPR} is as close to zero as possible. If there are two such {var}, pick the larger {var}.")
    def _(anode, env0):
        [let_var, num_expr, var2, var3] = anode.children
        assert same_source_text(var2, let_var)
        assert same_source_text(var3, let_var)
        new_env = env0.plus_new_entry(let_var, T_MathInteger_)
        new_env.assert_expr_is_of_type(num_expr, T_MathReal_)
        return new_env

    # Let {var} and {var} ... be ...

    @nv.put(r"{COMMAND} : Let {var} and {var} be the indirection values provided when this binding for {var} was created.")
    def _(anode, env0):
        [m_var, n2_var, n_var] = anode.children
        env0.assert_expr_is_of_type(n_var, T_String)
        return env0.plus_new_entry(m_var, T_Module_Record).plus_new_entry(n2_var, T_String)

    @nv.put(r"{COMMAND} : Let {var} and {var} be integers such that {CONDITION} and for which {NUM_EXPR} is as close to zero as possible. If there are two such sets of {var} and {var}, pick the {var} and {var} for which {PRODUCT} is larger.")
    def _(anode, env0):
        [e_var, n_var, cond, num_expr, e_var2, n_var2, e_var3, n_var3, product] = anode.children
        assert same_source_text(e_var2, e_var)
        assert same_source_text(e_var3, e_var)
        assert same_source_text(n_var2, n_var)
        assert same_source_text(n_var3, n_var)
        new_env = env0.plus_new_entry(e_var, T_MathInteger_).plus_new_entry(n_var, T_MathInteger_)
        (t_env, f_env) = tc_cond(cond, new_env)
        t_env.assert_expr_is_of_type(num_expr, T_MathReal_)
        t_env.assert_expr_is_of_type(product, T_MathReal_)
        return t_env

    @nv.put(r"{COMMAND} : Let {var}, {var}, and {var} be integers such that {CONDITION}. If there are multiple possibilities for {var}, choose the value of {var} for which {EX} is closest in value to {EX}. If there are two such possible values of {var}, choose the one that is even. Note that {var} is the number of digits in the representation of {var} using radix {var} and that {var} is not divisible by {var}.")
    @nv.put(r"{COMMAND} : Let {var}, {var}, and {var} be integers such that {CONDITION}. Note that the decimal representation of {var} has {SUM} digits, {var} is not divisible by 10, and the least significant digit of {var} is not necessarily uniquely determined by these criteria.")
    @nv.put(r"{COMMAND} : Let {var}, {var}, and {var} be integers such that {CONDITION}. Note that {var} is the number of digits in the representation of {var} using radix {var}, that {var} is not divisible by {var}, and that the least significant digit of {var} is not necessarily uniquely determined by these criteria.")
    def _(anode, env0):
        [vara, varb, varc, cond] = anode.children[0:4]
        env_for_cond = (
            env0.plus_new_entry(vara, T_MathInteger_)
                .plus_new_entry(varb, T_MathInteger_)
                .plus_new_entry(varc, T_MathInteger_)
        )
        (t_env, f_env) = tc_cond(cond, env_for_cond)
        return env_for_cond

#> These aliases are reference-like in that both _x_ and _someValue_ refer to the same underlying data
#> and modifications to either are visible to both.
#> Algorithm steps that want to avoid this reference-like behaviour
#> should explicitly make a copy of the right-hand side:
#> “Let _x_ be a copy of _someValue_” creates a shallow copy of _someValue_.

    @exprd.put(r"{EXPR} : a copy of {var}")
    def _(expr, env0, _):
        [var] = expr.children
        (t, env1) = tc_expr(var, env0); assert env1 is env0
        return (t, env1)

#> Once declared, an alias may be referenced in any subsequent steps
#> and must not be referenced from steps prior to the alias's declaration.

    @exprd.put(r'{SETTABLE} : {var}')
    def _(expr, env0, _):
        [var] = expr.children
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

# ------------------------------------------------------------------------------
# (there are other ways to declare an alias)

    @exprd.put(r'{EXPR} : {EX}, where {var} is {EX}')
    def _(expr, env0, _):
        [exa, var, exb] = expr.children
        (exb_type, env1) = tc_expr(exb, env0); assert env1 is env0
        env2 = env1.plus_new_entry(var, exb_type)
        (exa_type, env3) = tc_expr(exa, env2)
        return (exa_type, env3)

    @exprd.put(r'{EXPR} : {EX}, where {var} is {EX} and {var} is {EX}')
    @exprd.put(r'{EXPR} : {EX}, where {var} is {EX}, and {var} is {EX}')
    def _(expr, env0, _):
        [ex3, var2, ex2, var1, ex1] = expr.children

        (ex1_type, ex1_env) = tc_expr(ex1, env0); assert ex1_env is env0
        env1 = ex1_env.plus_new_entry(var1, ex1_type)

        (ex2_type, ex2_env) = tc_expr(ex2, env1); assert ex2_env is env1
        env2 = ex2_env.plus_new_entry(var2, ex2_type)

        (ex3_type, ex3_env) = tc_expr(ex3, env2); assert ex3_env is env2
        return (ex3_type, ex3_env)

# ------------------------------------------------------------------------------
#> Aliases may be modified using the form “Set _x_ to _someOtherValue_”.</p>

if 1:
    @nv.put(r'{COMMAND} : Set {SETTABLE} to {EXPR}.')
    @nv.put(r'{COMMAND} : Set {SETTABLE} to {MULTILINE_EXPR}')
    @nv.put(r'{SMALL_COMMAND} : set {SETTABLE} to {EXPR}')
    def _(anode, env0):
        [settable, expr] = anode.children
        return env0.set_A_to_B(settable, expr)

    @nv.put(r'{COMMAND} : Set {DOTTING} as described in {h_emu_xref}.')
    @nv.put(r'{COMMAND} : Set {DOTTING} as specified in {h_emu_xref}.')
    @nv.put(r'{COMMAND} : Set {DOTTING} to the definition specified in {h_emu_xref}.')
    def _(anode, env0):
        [dotting, emu_xref] = anode.children

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
            return env1.with_expr_type_narrowed(base_var, implied_base_t)
        elif curr_base_t == T_bound_function_exotic_object_ | T_Proxy_exotic_object_ | T_other_function_object_ and implied_base_t == T_constructor_object_:
            return env1.with_expr_type_replaced(base_var, implied_base_t)
        elif curr_base_t == implied_base_t:
            return env1
        else:
            assert 0

# ------------------------------------------------------------------------------
# (This section is where "Return" steps should be mentioned?)

if 1:
    @nv.put(r"{COMMAND} : Return {EXPR}.")
    @nv.put(r"{COMMAND} : Return {EXPR}. This may be of type Reference.")
    @nv.put(r"{COMMAND} : Return {MULTILINE_EXPR}")
    @nv.put(r"{SMALL_COMMAND} : return {EXPR}")
    def _(anode, env0):
        [expr] = anode.children
        (t1, env1) = tc_expr(expr, env0)
        # assert env1 is env0
        if False and trace_this_op:
            print("Return command's expr has type", t1)
        proc_add_return(env1, t1, anode)
        return None

# ------------------------------------------------------------------------------
# (This section is where "Note" steps should be mentioned?)

if 1:
    @nv.put(r'{COMMAND} : {note}')
    def _(anode, env0):
        return env0

# ------------------------------------------------------------------------------
# (This section is where conditions should be mentioned?)

    @condd.put(r'{CONDITION} : {CONDITION_1}')
    @condd.put(r'{CONDITION_1} : {TYPE_TEST}')
    @condd.put(r'{CONDITION_1} : {NUM_COMPARISON}')
    def _(cond, env0, asserting):
        [child] = cond.children
        return tc_cond(child, env0, asserting)

    @condd.put(r"{CONDITION} : either {CONDITION_1} or {CONDITION_1}")
    @condd.put(r"{CONDITION} : {CONDITION_1} or if {CONDITION_1}")
    @condd.put(r"{CONDITION} : {CONDITION_1} or {CONDITION_1} or {CONDITION_1} or {CONDITION_1}")
    @condd.put(r"{CONDITION} : {CONDITION_1} or {CONDITION_1} or {CONDITION_1}")
    @condd.put(r"{CONDITION} : {CONDITION_1} or {CONDITION_1}")
    @condd.put(r"{CONDITION} : {CONDITION_1}, or if {CONDITION_1}")
    @condd.put(r"{CONDITION} : {CONDITION_1}, or {CONDITION_1}")
    @condd.put(r"{CONDITION} : {CONDITION_1}, {CONDITION_1}, or {CONDITION_1}")
    @condd.put(r"{CONDITION} : {CONDITION_1}, {CONDITION_1}, {CONDITION_1}, or {CONDITION_1}")
    def _(cond, env0, asserting):
        logical = ('or', cond.children)
        return tc_logical(logical, env0, asserting)

    @condd.put(r"{CONDITION} : {CONDITION_1} and if {CONDITION_1}")
    @condd.put(r'{CONDITION} : {CONDITION_1} and {CONDITION_1}')
    @condd.put(r"{CONDITION} : {CONDITION_1} and {CONDITION_1} and {CONDITION_1}")
    @condd.put(r"{CONDITION} : {CONDITION_1}, {CONDITION_1}, and {CONDITION_1}")
    @condd.put(r'{CONDITION} : {CONDITION_1}, {CONDITION_1}, {CONDITION_1}, and {CONDITION_1}')
    def _(cond, env0, asserting):
        logical = ('and', cond.children)
        return tc_logical(logical, env0, asserting)

    @condd.put(r"{CONDITION} : {CONDITION_1}, or if {CONDITION_1} and {CONDITION_1}")
    def _(cond, env0, asserting):
        [conda, condb, condc] = cond.children
        logical = (
            'or',
            [
                conda,
                ('and', [condb, condc])
            ]
        )
        return tc_logical(logical, env0, asserting)

    @condd.put(r"{CONDITION} : {CONDITION_1} or {CONDITION_1} <ins>and {CONDITION_1}</ins>")
    def _(cond, env0, asserting):
        [a, b, c] = cond.children
        logical = (
            'and',
            [
                ('or', [a, b]),
                c
            ]
        )
        return tc_logical(logical, env0, asserting)

    @condd.put(r"{CONDITION} : {CONDITION_1} and {CONDITION_1} or {CONDITION_1} and {CONDITION_1}")
    @condd.put(r"{CONDITION} : {CONDITION_1} and {CONDITION_1}, or if {CONDITION_1} and {CONDITION_1}")
    @condd.put(r"{CONDITION} : {CONDITION_1} and {CONDITION_1}, or {CONDITION_1} and {CONDITION_1}")
    def _(cond, env0, asserting):
        [a, b, c, d] = cond.children
        logical = (
            'or',
            [
                ('and', [a, b]),
                ('and', [c, d]),
            ]
        )
        return tc_logical(logical, env0, asserting)

    @condd.put(r"{CONDITION} : ({NUM_COMPARISON} or {NUM_COMPARISON}) and ({NUM_COMPARISON} or {NUM_COMPARISON})")
    def _(cond, env0, asserting):
        [a, b, c, d] = cond.children
        logical = (
            'and',
            [
                ('or', [a, b]),
                ('or', [c, d]),
            ]
        )
        return tc_logical(logical, env0, asserting)

    @condd.put(r"{CONDITION} : {CONDITION_1} unless {CONDITION_1}")
    @condd.put(r"{CONDITION} : {CONDITION_1}, unless {CONDITION_1}")
    def _(cond, env0, asserting):
        [conda, condb] = cond.children
        tc_cond(conda, env0)
        tc_cond(condb, env0)
        return (env0, env0)

# ==============================================================================
#@ 5.2.1 Abstract Operations

if 1:
    @nv.put(r"{COMMAND} : Perform {PP_NAMED_OPERATION_INVOCATION}.")
    @nv.put(r"{COMMAND} : Perform {PP_NAMED_OPERATION_INVOCATION}. {note}")
    @nv.put(r"{SMALL_COMMAND} : perform {PP_NAMED_OPERATION_INVOCATION}")
    def _(anode, env0):
        noi = anode.children[0]
        (noi_t, env1) = tc_expr(noi, env0, expr_value_will_be_discarded=True)
        if noi_t.is_a_subtype_of_or_equal_to(T_tilde_unused_ | T_Undefined | T_tilde_empty_):
            pass
        else:
            if 0:
                # disable because it's noisy for no benefit?
                add_pass_error(
                    anode,
                    "`Perform/Call` discards `%s` value"
                    % str(noi_t)
                )
        return env1

    @exprd.put(r"{PP_NAMED_OPERATION_INVOCATION} : {NAMED_OPERATION_INVOCATION}")
    def _(expr, env0, expr_value_will_be_discarded):
        [noi] = expr.children
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

    @exprd.put(r"{NAMED_OPERATION_INVOCATION} : {h_emu_meta_start}{NAMED_OPERATION_INVOCATION}{h_emu_meta_end}")
    def _(expr, env0, _):
        [_, noi, _] = expr.children
        return tc_expr(noi, env0)

    @exprd.put(r"{NAMED_OPERATION_INVOCATION} : {PREFIX_PAREN} (see {h_emu_xref})")
    def _(expr, env0, _):
        [pp, _] = expr.children
        return tc_expr(pp, env0)

#> Abstract operations are typically referenced using a functional application style
#> such as OperationName(_arg1_, _arg2_).

if 1:
    @exprd.put(r'{PREFIX_PAREN} : {OPN_BEFORE_PAREN}({EXLIST_OPT})')
    def _(expr, env0, _):
        [opn_before_paren, arglist] = expr.children[0:2]
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

            elif callee_op_name in ['floor', 'truncate']:
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
                else:
                    add_pass_error(
                        arg,
                        f"expected a BigInt or a finite Number, got {arg_type}"
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
                    result_type = T_IntegralNumber_ | T_NegInfinityNumber_ | T_PosInfinityNumber_
                elif t.is_a_subtype_of_or_equal_to(T_ExtendedMathReal_):
                    result_type = T_FiniteNumber_ | T_NegInfinityNumber_ | T_PosInfinityNumber_
                elif t == T_TBD:
                    result_type = T_IntegralNumber_ # hm
                else:
                    add_pass_error(arg,
                        f"ERROR: arg is of type {t} but fancy_f requires ExtendedMathReal"
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
                        if t == T_MathInteger_ | T_tilde_empty_:
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

#> Some abstract operations are treated as
#> polymorphically dispatched methods of class-like specification abstractions.
#> Such method-like abstract operations are typically referenced
#> using a method application style such as _someValue_.OperationName(_arg1_, _arg2_).

# ==============================================================================
#@ 5.2.2 Syntax-Directed Operations

#> When an algorithm is associated with a grammar production,
#> it may reference the terminal and nonterminal symbols
#> of the production alternative
#> as if they were parameters of the algorithm.

if 1:
    @exprd.put(r"{PROD_REF} : the {nonterminal} of {LOCAL_REF}")
    def _(expr, env0, _):
        [nonterminal, var] = expr.children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        # XXX could check that t is a nonterminal that actually has a child of that type
        # but that requires having the whole grammar handy
        return (ptn_type_for(nonterminal), env0)

    @exprd.put(r'{PROD_REF} : this {nonterminal}')
    def _(expr, env0, _):
        [nonterminal] = expr.children
        # XXX check
        return (ptn_type_for(nonterminal), env0)

    @exprd.put(r'{PROD_REF} : {nonterminal}')
    def _(expr, env0, _):
        [nonterminal] = expr.children
        return (ptn_type_for(nonterminal), env0)

    @exprd.put(r"{PROD_REF} : {nonterminal} {var}")
    def _(expr, env0, _):
        [nonterminal, var] = expr.children
        t = ptn_type_for(nonterminal)
        env0.assert_expr_is_of_type(var, t)
        return (t, env0)

    @exprd.put(r'{PROD_REF} : the {ORDINAL} {nonterminal}')
    def _(expr, env0, _):
        [ordinal, nonterminal] = expr.children
        # XXX should check that the 'current' production has such.
        return (ptn_type_for(nonterminal), env0)

    @exprd.put(r'{PROD_REF} : the {nonterminal}')
    def _(expr, env0, _):
        nonterminal = expr.children[-1]
        return (ptn_type_for(nonterminal), env0)

    @exprd.put(r"{PROD_REF} : that {nonterminal}")
    def _(expr, env0, _):
        [nont] = expr.children
        return (ptn_type_for(nont), env0)

    @exprd.put(r"{PROD_REF} : this phrase")
    @exprd.put(r"{PROD_REF} : this production")
    def _(expr, env0, _):
        return (T_Parse_Node, env0)

    @exprd.put(r"{PROD_REF} : the derived {nonterminal}")
    def _(expr, env0, _):
        [nont] = expr.children
        return (T_Parse_Node, env0)

    @tbd.put('{VAL_DESC} : the {nonterminal} of an? {nonterminal}')
    def _(val_desc, env):
        [nont1, nont2] = val_desc.children
        return a_subset_of(ptn_type_for(nont1))

    @condd.put(r'{CONDITION_1} : {LOCAL_REF} is present')
    @condd.put(r'{CONDITION_1} : {LOCAL_REF} is not present')
    def _(cond, env0, asserting):
        [ex] = cond.children
        if ex.is_a('{PROD_REF}'):
            t = T_not_in_node
        elif ex.is_a('{var}'):
            # todo: get rid of this usage. (roll eyes at PR #953)
            t = T_not_passed # assuming it's a parameter
        else:
            assert 0, ex.source_text()
        copula = 'is a' if 'not present' in cond.prod.rhs_s else 'isnt a'
        return env0.with_type_test(ex, copula, t, asserting)

#> The <dfn>source text matched by</dfn> a grammar production
#> or Parse Node derived from it
#> is the portion of the source text
#> that starts at the beginning of the first terminal that participated in the match
#> and ends at the end of the last terminal that participated in the match.

#> Syntax-directed operations are invoked with a parse node and, optionally, other parameters ...

if 1:
    @exprd.put(r"{NAMED_OPERATION_INVOCATION} : the {cap_word} of {LOCAL_REF}")
    @exprd.put(r"{NAMED_OPERATION_INVOCATION} : the {cap_word} of {LOCAL_REF} (see {h_emu_xref})")
    @exprd.put(r"{NAMED_OPERATION_INVOCATION} : the {cap_word} of {LOCAL_REF} as defined in {h_emu_xref}")
    @exprd.put(r"{NAMED_OPERATION_INVOCATION} : {cap_word} of {LOCAL_REF}")
    @exprd.put(r"{NAMED_OPERATION_INVOCATION} : the result of performing {cap_word} on {EX}")
    def _(expr, env0, _):
        [callee, local_ref] = expr.children[0:2]
        callee_op_name = callee.source_text()
        if callee_op_name in ['UTF16EncodeCodePoint', 'UTF16SurrogatePairToCodePoint']:
            # An abstract operation that uses SDO-style invocation.
            return tc_ao_invocation(callee_op_name, [local_ref], expr, env0)
        else:
            return tc_sdo_invocation(callee_op_name, local_ref, [], expr, env0)

    @exprd.put(r"{NAMED_OPERATION_INVOCATION} : the {cap_word} of {LOCAL_REF} {WITH_ARGS}")
    @exprd.put(r"{NAMED_OPERATION_INVOCATION} : {cap_word} of {LOCAL_REF} {WITH_ARGS}")
    def _(expr, env0, _):
        [callee, local_ref, with_args] = expr.children
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

# ==============================================================================
#@ 5.2.3 Runtime Semantics

# ==============================================================================
#@ 5.2.3.2 Throw an Exception

if 1:
    @nv.put(r"{COMMAND} : Throw a {ERROR_TYPE} exception.")
    @nv.put(r"{SMALL_COMMAND} : throw a {ERROR_TYPE} exception because the structure is cyclical")
    @nv.put(r'{SMALL_COMMAND} : throw a {ERROR_TYPE} exception')
    def _(anode, env0):
        [error_type] = anode.children
        proc_add_return(env0, ThrowType(type_for_ERROR_TYPE(error_type)), anode)
        return None

# ==============================================================================
#@ 5.2.3.3 ReturnIfAbrupt

if 1:
    @nv.put(r"{COMMAND} : ReturnIfAbrupt({EX}).")
    @nv.put(r"{SMALL_COMMAND} : ReturnIfAbrupt({var})")
    def _(anode, env0):
        [ex] = anode.children
        (ex_t, env1) = tc_expr(ex, env0); assert env1 is env0
        if ex_t == T_TBD:
            # Doesn't make sense to compare_types
            # And a proc_add_return(..., T_TBD) wouldn't help
            return env1
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
            return env1.with_expr_type_narrowed(ex, normal_part_of_ex_t)

# ==============================================================================
#@ 5.2.3.4 ReturnIfAbrupt Shorthands

if 1:
    @exprd.put(r'{PP_NAMED_OPERATION_INVOCATION} : ? {NAMED_OPERATION_INVOCATION}')
    @exprd.put(r"{EX} : ? {DOTTING}")
    @exprd.put(r"{EX} : ? {var}")
    def _(expr, env0, _):
        [operand] = expr.children
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

        env2 = env1
        if str(operand.prod) == '{NAMED_OPERATION_INVOCATION} : {PREFIX_PAREN}':
            [pp] = operand.children
            assert str(pp.prod).startswith(r'{PREFIX_PAREN} : {OPN_BEFORE_PAREN}({EXLIST_OPT})')
            [opn_before_paren, exlist_opt] = pp.children[0:2]
            prefix = opn_before_paren.source_text()

            if prefix == 'RequireInternalSlot':
                # This amounts to a type-test.
                # I.e., in the not-returning-early env resulting from this NAMED_OPERATION_INVOCATION,
                # we can narrow the type of the first arg to RequireInternalSlot.
                (obj_arg, slotname_arg) = exes_in_exlist_opt(exlist_opt)

                t = {
                    '[[ArrayBufferData]]'       : T_ArrayBuffer_object_ | T_SharedArrayBuffer_object_,
                    '[[AsyncGeneratorContext]]' : T_AsyncGenerator_object_,
                    '[[AsyncGeneratorQueue]]'   : T_AsyncGenerator_object_,
                    '[[AsyncGeneratorState]]'   : T_AsyncGenerator_object_,
                    '[[Cells]]'                 : T_FinalizationRegistry_object_,
                    '[[DataView]]'              : T_Object,
                    '[[GeneratorBrand]]'        : T_Object,
                    '[[GeneratorState]]'        : T_Object,
                    '[[MapData]]'               : T_Object,
                    '[[RegExpMatcher]]'         : T_Object,
                    '[[SetData]]'               : T_Object,
                    '[[TypedArrayName]]'        : T_TypedArray_object_,
                    '[[WeakMapData]]'           : T_WeakMap_object_,
                    '[[WeakRefTarget]]'         : T_WeakRef_object_,
                    '[[WeakSetData]]'           : T_WeakSet_object_,
                }[slotname_arg.source_text()]

                env2 = env1.with_expr_type_narrowed(obj_arg, t)

            elif prefix in ['ValidateTypedArray', 'ValidateIntegerTypedArray']:
                obj_arg = exes_in_exlist_opt(exlist_opt)[0]
                env2 = env1.with_expr_type_narrowed(obj_arg, T_TypedArray_object_)

            elif prefix == 'GeneratorValidate':
                gen_arg = exes_in_exlist_opt(exlist_opt)[0]
                env2 = env1.with_expr_type_narrowed(gen_arg, T_Object)

        return (normal_part_of_type, env2)

    @exprd.put(r'{PP_NAMED_OPERATION_INVOCATION} : ! {NAMED_OPERATION_INVOCATION}')
    def _(expr, env0, _):
        [noi] = expr.children
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

# ==============================================================================
#@ 5.2.3.5 Implicit Normal Completion

# ==============================================================================
#@ 5.2.4 Static Semantics

#> A special kind of static semantic rule is an Early Error Rule.

if 1:
    @nv.put(r"{EE_RULE} : It is a Syntax Error if {CONDITION}.")
    @nv.put(r"{EE_RULE} : It is an early Syntax Error if {CONDITION}.")
    def _(anode, env0):
        [cond] = anode.children
        tc_cond(cond, env0, False)
        return None

    @nv.put(r"{EE_RULE} : <p>{_indent_}{nlai}It is a Syntax Error if {LOCAL_REF} is<br>{nlai}{h_emu_grammar}<br>{nlai}and {LOCAL_REF} ultimately derives a phrase that, if used in place of {LOCAL_REF}, would produce a Syntax Error according to these rules. This rule is recursively applied.{_outdent_}{nlai}</p>")
    def _(anode, env0):
        [local_ref1, h_emu_grammar, local_ref2, local_ref3] = anode.children
        env0.assert_expr_is_of_type(local_ref1, T_Parse_Node)
        env0.assert_expr_is_of_type(local_ref2, T_Parse_Node)
        env0.assert_expr_is_of_type(local_ref3, T_Parse_Node)
        return None

    @nv.put(r"{EE_RULE} : If {CONDITION}, the Early Error rules for {h_emu_grammar} are applied.")
    def _(anode, env0):
        [cond, h_emu_grammar] = anode.children
        tc_cond(cond, env0, False)
        return None

    @nv.put(r"{EE_RULE} : If {CONDITION}, it is a Syntax Error if {CONDITION}.")
    def _(anode, env0):
        [conda, condb] = anode.children
        (tenv, fenv) = tc_cond(conda, env0, False)
        tc_cond(condb, tenv, False)
        return None

    @nv.put(r"{EE_RULE} : <p>It is a Syntax Error if {CONDITION_1} and the following algorithm returns {BOOL_LITERAL}:</p>{nlai}{h_emu_alg}")
    def _(anode, env0):
        [cond, bool_lit, h_emu_alg] = anode.children
        tc_cond(cond, env0)
        # XXX should check h_emu_alg
        return None

    @nv.put(r"{EE_RULE} : It is a Syntax Error if {CONDITION}. Additional early error rules for {G_SYM} within direct eval are defined in {h_emu_xref}.")
    @nv.put(r"{EE_RULE} : It is a Syntax Error if {CONDITION}. Additional early error rules for {G_SYM} in direct eval are defined in {h_emu_xref}.")
    def _(anode, env0):
        [cond, g_sym, h_emu_xref] = anode.children
        tc_cond(cond, env0)
        return None

    @nv.put(r"{EE_RULE} : It is a Syntax Error if {CONDITION}. This rule is not applied if {CONDITION}.")
    def _(anode, env0):
        [conda, condb] = anode.children
        (t_env, f_env) = tc_cond(condb, env0)
        tc_cond(conda, f_env)
        return None

    @nv.put(r"{EE_RULE} : For each {nonterminal} {var} in {NAMED_OPERATION_INVOCATION}: It is a Syntax Error if {CONDITION}.")
    def _(anode, env0):
        [nont, var, noi, cond] = anode.children
        t = ptn_type_for(nont)
        env1 = env0.ensure_expr_is_of_type(noi, ListType(t))
        env2 = env1.plus_new_entry(var, t)
        tc_cond(cond, env2)
        return None

# ==============================================================================
#@ 5.2.5 Mathematical Operations

#> This specification makes reference to these kinds of numeric values:
#>  -- <dfn>Mathematical values</dfn>: Arbitrary real numbers, used as the default numeric type.
#>  -- <dfn>Extended mathematical values</dfn>: Mathematical values together with +∞ and -∞.
#>  -- <em>Numbers</em>: IEEE 754-2019 double-precision floating point values.
#>  -- <em>BigInts</em>: ECMAScript language values representing arbitrary integers in a one-to-one correspondence.

if 1:
    tbd['{VAL_DESC} : a mathematical value'] = T_MathReal_
    tbd['{VAL_DESC} : a non-negative extended mathematical value'] = a_subset_of(T_MathReal_ | T_MathPosInfinity_)

#> Numeric operators such as +, ×, =, and ≥ refer to those operations
#> as determined by the type of the operands.
#> When applied to mathematical values,
#>      the operators refer to the usual mathematical operations.
#> When applied to extended mathematical values,
#>      the operators refer to the usual mathematical operations over the extended real numbers;
#>      indeterminate forms are not defined
#>      and their use in this specification should be considered an editorial error.
#> When applied to Numbers,
#>      the operators refer to the relevant operations within IEEE 754-2019.
#> When applied to BigInts,
#>      the operators refer to the usual mathematical operations
#>      applied to the mathematical value of the BigInt.
#> ...
#> Numeric operators applied to mixed-type operands
#> (such as a Number and a mathematical value)
#> are not defined and should be considered an editorial error in this specification.

if 1:
    @exprd.put(r'{SUM} : {TERM} {SUM_OPERATOR} {TERM}')
    @exprd.put(r"{SUM} : {SUM} {SUM_OPERATOR} {TERM}")
    @exprd.put(r'{PRODUCT} : {FACTOR} {PRODUCT_OPERATOR} {FACTOR}')
    def _(expr, env0, _):
        [a, op, b] = expr.children
        (a_t, env1) = tc_expr(a, env0)
        (b_t, env2) = tc_expr(b, env1)
        op_st = op.source_text()

        def type_arithmetic(a_mt, op_st, b_mt, a, b):
            triple = (a_mt, op_st, b_mt)
            result_t = {

                # --------

                # Mathematical values:

                (T_ExtendedMathReal_, 'modulo', T_MathInteger_): 'ST of A includes infinities',
                (T_ExtendedMathReal_, 'modulo', T_MathReal_   ): 'ST of A includes infinities',

                (T_ExtendedMathReal_, '×'      , T_ExtendedMathReal_): T_ExtendedMathReal_,
                (T_ExtendedMathReal_, '×'      , T_MathInteger_     ): T_ExtendedMathReal_,
                (T_ExtendedMathReal_, '+'      , T_ExtendedMathReal_): T_ExtendedMathReal_,
                (T_ExtendedMathReal_, '+'      , T_MathInteger_     ): T_ExtendedMathReal_,
                (T_ExtendedMathReal_, '-'      , T_MathInteger_     ): T_ExtendedMathReal_,
                (T_ExtendedMathReal_, '/'      , T_ExtendedMathReal_): T_ExtendedMathReal_,
                (T_ExtendedMathReal_, '/'      , T_MathInteger_     ): T_ExtendedMathReal_,
                (T_MathInteger_     , '×'      , T_ExtendedMathReal_): T_ExtendedMathReal_,
                (T_MathInteger_     , '+'      , T_ExtendedMathReal_): T_ExtendedMathReal_,

                (T_MathPosInfinity_ , '+'      , T_MathReal_        ): T_MathPosInfinity_,

                (T_MathInteger_    , '+'      , T_MathNegInfinity_): T_MathNegInfinity_,

                (T_MathInteger_, '×'      , T_MathReal_   ): T_MathReal_,
                (T_MathInteger_, '+'      , T_MathReal_   ): T_MathReal_,
                (T_MathInteger_, '-'      , T_MathReal_   ): T_MathReal_,
                (T_MathInteger_, '/'      , T_MathInteger_): T_MathReal_,
                (T_MathReal_   , '×'      , T_MathInteger_): T_MathReal_,
                (T_MathReal_   , '×'      , T_MathReal_   ): T_MathReal_,
                (T_MathReal_   , '+'      , T_MathInteger_): T_MathReal_,
                (T_MathReal_   , '+'      , T_MathReal_   ): T_MathReal_,
                (T_MathReal_   , '-'      , T_MathInteger_): T_MathReal_,
                (T_MathReal_   , '-'      , T_MathReal_   ): T_MathReal_,
                (T_MathReal_   , '/'      , T_MathInteger_): T_MathReal_,
                (T_MathReal_   , '/'      , T_MathReal_   ): T_MathReal_,
                (T_MathReal_   , 'modulo' , T_MathInteger_): T_MathReal_,
                (T_MathReal_   , 'modulo' , T_MathReal_   ): T_MathReal_,

                (T_MathInteger_, '×'      , T_MathInteger_): T_MathInteger_,
                (T_MathInteger_, '+'      , T_MathInteger_): T_MathInteger_,
                (T_MathInteger_, '-'      , T_MathInteger_): T_MathInteger_,
                (T_MathInteger_, 'modulo' , T_MathInteger_): T_MathInteger_,
                (T_MathInteger_, 'plus'   , T_MathInteger_): T_MathInteger_,
                (T_MathInteger_, 'times'  , T_MathInteger_): T_MathInteger_,
                (T_code_point_ , '-'      , T_MathInteger_): T_MathInteger_, # warn
                (T_code_unit_  , '-'      , T_MathInteger_): T_MathInteger_, # warn

                # --------

                # Numbers:

                (T_Number       , '-'      , T_IntegralNumber_): 'A could be NaN',

                (T_FiniteNumber_     , '×'      , T_NegInfinityNumber_): T_NegInfinityNumber_, # warn [assuming finite is > 0]
                (T_FiniteNumber_     , '+'      , T_NegInfinityNumber_): T_NegInfinityNumber_, # warn
                (T_FiniteNumber_     , '-'      , T_PosInfinityNumber_): T_NegInfinityNumber_, # warn
                (T_NegInfinityNumber_, '+'      , T_IntegralNumber_   ): T_NegInfinityNumber_, # warn
                (T_NegInfinityNumber_, '-'      , T_IntegralNumber_   ): T_NegInfinityNumber_, # warn
                (T_NegInfinityNumber_, '/'      , T_FiniteNumber_     ): T_NegInfinityNumber_, # warn [assuming finite is > 0]

                (T_FiniteNumber_     , '×'      , T_PosInfinityNumber_): T_PosInfinityNumber_, # warn [assuming finite is > 0]
                (T_FiniteNumber_     , '+'      , T_PosInfinityNumber_): T_PosInfinityNumber_, # warn
                (T_FiniteNumber_     , '-'      , T_NegInfinityNumber_): T_PosInfinityNumber_, # warn
                (T_PosInfinityNumber_, '+'      , T_IntegralNumber_   ): T_PosInfinityNumber_, # warn
                (T_PosInfinityNumber_, '-'      , T_IntegralNumber_   ): T_PosInfinityNumber_, # warn
                (T_PosInfinityNumber_, '/'      , T_FiniteNumber_     ): T_PosInfinityNumber_, # warn [assuming finite is > 0]

                (T_FiniteNumber_  , '×'      , T_FiniteNumber_  ): T_FiniteNumber_,
                (T_FiniteNumber_  , '+'      , T_FiniteNumber_  ): T_FiniteNumber_,
                (T_FiniteNumber_  , '+'      , T_IntegralNumber_): T_FiniteNumber_,
                (T_FiniteNumber_  , '-'      , T_FiniteNumber_  ): T_FiniteNumber_,
                (T_FiniteNumber_  , '-'      , T_IntegralNumber_): T_FiniteNumber_,
                (T_FiniteNumber_  , '/'      , T_FiniteNumber_  ): T_FiniteNumber_, # assuming that b isn't 0
                (T_IntegralNumber_, '/'      , T_FiniteNumber_  ): T_FiniteNumber_,

                (T_IntegralNumber_, '+', T_IntegralNumber_): T_IntegralNumber_,
                (T_IntegralNumber_, '-', T_IntegralNumber_): T_IntegralNumber_,

                # --------

                # BigInts:

                (T_BigInt, '×'      , T_BigInt): T_BigInt,
                (T_BigInt, '-'      , T_BigInt): T_BigInt,

                # --------

                # misc:

                (T_not_set     , '×'      , T_MathInteger_): 'A is non-numeric',
                (T_tilde_empty_, '-'      , T_MathInteger_): 'A is non-numeric',

            }[triple]

            if result_t == 'A is non-numeric':
                add_pass_error(a, f"ST of operand is {a_t}, which includes {a_mt}, which is non-numeric")
                result_t = T_MathInteger_ # XXX
            elif result_t == 'A could be NaN':
                add_pass_error(a, f"ST of operand is {a_t}, which includes *NaN*, which you can't do arithmetic on")
                result_t = T_Number
            elif result_t == 'B could be NaN':
                add_pass_error(b, f"ST of operand is {b_t}, which includes *NaN*, which you can't do arithmetic on")
                result_t = T_Number
            elif result_t == 'ST of A includes infinities':
                add_pass_error(a, "operand could be infinite, which doesn't make sense with 'modulo'")
                result_t = T_MathInteger_
            else:
                assert isinstance(result_t, Type)

            return result_t
                    
        result_t = T_0
        for a_mt in a_t.set_of_types():
            for b_mt in b_t.set_of_types():
                result_t = result_t | type_arithmetic(a_mt, op_st, b_mt, a, b)
        return (result_t, env2)

    @exprd.put(r"{PRODUCT} : {UNARY_OPERATOR}{FACTOR}")
    def _(expr, env0, _):
        ex = expr.children[-1]
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

    @exprd.put(r'{EXPR} : the negative of {EX}')
    def _(expr, env0, _):
        [ex] = expr.children
        (ex_t, env1) = tc_expr(ex, env0); assert env1 is env0
        assert ex_t == T_TBD or ex_t == T_MathInteger_
        return (ex_t, env0)

    @exprd.put(r"{PRODUCT} : the negation of {EX}")
    def _(expr, env0, _):
        [ex] = expr.children
        env0.assert_expr_is_of_type(ex, T_MathReal_)
        return (T_MathReal_, env0)

    @exprd.put(r"{EX} : the remainder of dividing {EX} by {EX}")
    @exprd.put(r"{EX} : The remainder of dividing {EX} by {EX}")
    def _(expr, env0, _):
        [aex, bex] = expr.children
        env0.assert_expr_is_of_type(aex, T_MathInteger_)
        env0.assert_expr_is_of_type(bex, T_MathInteger_)
        return (T_MathInteger_, env0)

    @exprd.put(r"{PRODUCT} : the quotient {FACTOR} / {FACTOR}")
    def _(expr, env0, _):
        [vara, varb] = expr.children
        env1 = env0.ensure_expr_is_of_type(vara, T_MathReal_)
        env2 = env1.ensure_expr_is_of_type(varb, T_MathReal_)
        return (T_MathReal_, env2)

    @exprd.put(r"{EX} : {EX}, rounding down to the nearest integer, including for negative numbers")
    def _(expr, env0, _):
        [ex] = expr.children
        env0.assert_expr_is_of_type(ex, T_MathReal_)
        return (T_MathInteger_, env0)

    @exprd.put(r"{FACTOR} : {BASE}<sup>{EX}</sup>")
    def _(expr, env0, _):
        [base, exponent] = expr.children
        (base_t, env1) = tc_expr(base, env0); assert env1 is env0
        if base_t == T_MathInteger_:
            env1 = env0.ensure_expr_is_of_type(exponent, T_MathReal_ | T_BigInt)
        else:
            assert 0, base_t
        return (base_t, env1) # XXX unless exponent is negative

    @exprd.put(r"{NUM_EXPR} : {EX} raised to the power {EX}")
    def _(expr, env0, _):
        [a, b] = expr.children
        env0.assert_expr_is_of_type(a, T_MathInteger_)
        env0.assert_expr_is_of_type(b, T_MathInteger_)
        return (T_MathInteger_, env0) # unless exponent is negative

    @exprd.put(r"{EXPR} : the result of raising {EX} to the {EX} power")
    def _(expr, env0, _):
        [avar, bvar] = expr.children
        env1 = env0.ensure_expr_is_of_type(avar, T_MathReal_)
        env2 = env0.ensure_expr_is_of_type(bvar, T_MathReal_)
        return (T_MathReal_, env2)

    @exprd.put(r'{NUM_EXPR} : π / 2')
    @exprd.put(r'{NUM_EXPR} : π / 4')
    @exprd.put(r'{NUM_EXPR} : π')
    @exprd.put(r'{NUM_EXPR} : 3π / 4')
    @exprd.put(r'{NUM_EXPR} : -π / 2')
    @exprd.put(r'{NUM_EXPR} : -π / 4')
    @exprd.put(r'{NUM_EXPR} : -π')
    @exprd.put(r'{NUM_EXPR} : -3π / 4')
    def _(expr, env0, _):
        [] = expr.children
        return (T_MathReal_, env0)

    @exprd.put(r"{EXPR} : the result of the {MATH_FUNC} of {EX}")
    def _(expr, env0, _):
        [math_func, ex] = expr.children
        env1 = env0.ensure_expr_is_of_type(ex, T_Number | T_MathReal_)
        return (T_MathReal_, env1)

    @exprd.put(r"{EXPR} : the result of subtracting 1 from the exponential function of {EX}")
    def _(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_MathReal_)
        return (T_MathReal_, env1)

    @exprd.put(r"{EXPR} : the square root of the sum of squares of the mathematical values of the elements of {var}")
    def _(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_List)
        return (T_MathReal_, env0)

    @exprd.put(r"{EXPR} : an implementation-defined choice of either {var} or {var}")
    def _(expr, env0, _):
        [vara, varb] = expr.children
        env0.assert_expr_is_of_type(vara, T_MathReal_)
        env0.assert_expr_is_of_type(varb, T_MathReal_)
        return (T_MathReal_, env0)

# comparisons:

    @condd.put(r'{CONDITION_1} : {var} is odd')
    def _(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_MathInteger_)
        return (env0, env0)

    @condd.put(r"{NUM_COMPARISON} : {NUM_COMPARAND} is 10 or less")
    def _(cond, env0, asserting):
        [x] = cond.children
        env0.assert_expr_is_of_type(x, T_MathInteger_)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {NAMED_OPERATION_INVOCATION} is larger than {NAMED_OPERATION_INVOCATION}")
    def _(cond, env0, asserting):
        [noia, noib] = cond.children
        env0.assert_expr_is_of_type(noia, T_MathInteger_)
        env0.assert_expr_is_of_type(noib, T_MathInteger_)
        return (env0, env0)

    @condd.put(r'{NUM_COMPARISON} : {NUM_COMPARAND} {NUM_COMPARATOR} {NUM_COMPARAND} {NUM_COMPARATOR} {NUM_COMPARAND}')
    def _(cond, env0, asserting):
        [a, _, b, _, c] = cond.children
        env0.assert_expr_is_of_type(a, T_MathInteger_)
        env1 = env0.ensure_expr_is_of_type(b, T_MathInteger_ | T_MathNegInfinity_ | T_MathPosInfinity_)
        env0.assert_expr_is_of_type(c, T_MathInteger_)
        env2 = env1.with_expr_type_narrowed(b, T_MathInteger_)
        return (env2, env2)

    @condd.put(r"{NUM_COMPARISON} : {NUM_COMPARAND} {NUM_COMPARATOR} {NUM_COMPARAND}")
    def _(cond, env0, asserting):
        [a, op, b] = cond.children
        (a_t, env1) = tc_expr(a, env0);
        (b_t, env2) = tc_expr(b, env1);
        op_st = op.source_text()

        t_envs = []
        f_envs = []

        a_memtypes = sorted(a_t.set_of_types())
        b_memtypes = sorted(b_t.set_of_types())

        for a_memtype in a_memtypes:
            for b_memtype in b_memtypes:
                triple = (a_memtype, op_st, b_memtype)
                something = {

                    # always error:
                    (T_BigInt            , '>'   , T_FiniteNumber_     ): 'E',
                    (T_BigInt            , '>'   , T_NegInfinityNumber_): 'E',
                    (T_BigInt            , '>'   , T_PosInfinityNumber_): 'E',
                    (T_BigInt            , '&lt;', T_FiniteNumber_     ): 'E',
                    (T_BigInt            , '&lt;', T_NegInfinityNumber_): 'E',
                    (T_BigInt            , '&lt;', T_PosInfinityNumber_): 'E',
                    (T_BigInt            , '≠'   , T_Number            ): 'E',
                    (T_FiniteNumber_     , '>'   , T_BigInt            ): 'E',
                    (T_FiniteNumber_     , '&lt;', T_BigInt            ): 'E',
                    (T_IntegralNumber_   , '≠'   , T_BigInt            ): 'E',
                    (T_NegInfinityNumber_, '>'   , T_BigInt            ): 'E',
                    (T_NegInfinityNumber_, '&lt;', T_BigInt            ): 'E',
                    (T_PosInfinityNumber_, '&lt;', T_BigInt            ): 'E',
                    (T_PosInfinityNumber_, '>'   , T_BigInt            ): 'E',
                    (T_tilde_empty_      , '>'   , T_MathInteger_      ): 'E',
                    #
                    # Comparisons between Number and BigInt mostly come from
                    # %TypedArray%.prototype.sort, which has:
                    # 1. Assert: _x_ is a Number and _y_ is a Number, or _x_ is a BigInt and _y_ is a BigInt.
                    # which this STA doesn't represent well.
                    #
                    # Also Atomics.wait (`If _v_ ≠ _w_, ...`)

                    # could be error:
                    (T_IntegralNumber_, '≠', T_Number   ): 'TFE', # because the Number might be NaN
                    (T_IntegralNumber_, '≥', T_Tangible_): 'TFE',

                    # ------------
                    # Mathematical:

                    # always true:
                    (T_MathInteger_    , '≤'   , T_MathPosInfinity_): 'T',
                    (T_MathNegInfinity_, '≤'   , T_MathInteger_    ): 'T',
                    (T_MathNegInfinity_, '&lt;', T_MathInteger_    ): 'T',
                    (T_MathPosInfinity_, '≥'   , T_MathInteger_    ): 'T',
                    (T_MathPosInfinity_, '>'   , T_FiniteNumber_   ): 'T',
                    (T_MathPosInfinity_, '>'   , T_MathInteger_    ): 'T',

                    # always false:
                    (T_MathNegInfinity_, '≥'   , T_MathInteger_): 'F',
                    (T_MathNegInfinity_, '='   , T_MathInteger_): 'F',
                    (T_MathPosInfinity_, '≤'   , T_MathInteger_): 'F',
                    (T_MathPosInfinity_, '&lt;', T_MathInteger_): 'F',
                    (T_MathPosInfinity_, '='   , T_MathInteger_): 'F',

                    # can be true or false:
                    (T_ExtendedMathReal_, '≥'   , T_MathInteger_     ): 'TF',
                    (T_ExtendedMathReal_, '≤'   , T_MathInteger_     ): 'TF',
                    (T_ExtendedMathReal_, '&lt;', T_ExtendedMathReal_): 'TF',
                    (T_ExtendedMathReal_, '&lt;', T_MathInteger_     ): 'TF',
                    (T_MathInteger_     , '≥'   , T_MathInteger_     ): 'TF',
                    (T_MathInteger_     , '>'   , T_MathInteger_     ): 'TF',
                    (T_MathInteger_     , '≤'   , T_MathInteger_     ): 'TF',
                    (T_MathInteger_     , '&lt;', T_ExtendedMathReal_): 'TF',
                    (T_MathInteger_     , '&lt;', T_MathInteger_     ): 'TF',
                    (T_MathInteger_     , '≠'   , T_MathInteger_     ): 'TF',
                    (T_MathInteger_     , '≠'   , T_MathReal_        ): 'TF',
                    (T_MathInteger_     , '='   , T_MathInteger_     ): 'TF',
                    (T_MathReal_        , '≥'   , T_MathInteger_     ): 'TF',
                    (T_MathReal_        , '>'   , T_MathInteger_     ): 'TF',
                    (T_MathReal_        , '>'   , T_MathReal_        ): 'TF',
                    (T_MathReal_        , '&lt;', T_MathInteger_     ): 'TF',
                    (T_MathReal_        , '&lt;', T_MathReal_        ): 'TF',
                    (T_MathReal_        , '≠'   , T_MathInteger_     ): 'TF',
                    (T_MathReal_        , '='   , T_MathInteger_     ): 'TF',
                    (T_MathReal_        , '='   , T_MathReal_        ): 'TF',

                    (T_MathInteger_, 'is at least', T_MathInteger_): 'TF',

                    (T_code_point_ , '≤', T_MathInteger_): 'TF', # but deserves a warning

                    # -------
                    # Number:

                    # always true:
                    (T_FiniteNumber_     , '>'   , T_NegInfinityNumber_): 'T',
                    (T_FiniteNumber_     , '&lt;', T_PosInfinityNumber_): 'T',
                    (T_NegInfinityNumber_, '&lt;', T_FiniteNumber_     ): 'T',
                    (T_NegInfinityNumber_, '&lt;', T_IntegralNumber_   ): 'T',
                    (T_NegInfinityNumber_, '&lt;', T_PosInfinityNumber_): 'T',
                    (T_PosInfinityNumber_, '>'   , T_FiniteNumber_     ): 'T',
                    (T_PosInfinityNumber_, '>'   , T_IntegralNumber_   ): 'T',
                    (T_PosInfinityNumber_, '>'   , T_NegInfinityNumber_): 'T',

                    # always false:
                    (T_FiniteNumber_     , '>'   , T_PosInfinityNumber_): 'F',
                    (T_FiniteNumber_     , '&lt;', T_NegInfinityNumber_): 'F',
                    (T_NegInfinityNumber_, '>'   , T_FiniteNumber_     ): 'F',
                    (T_NegInfinityNumber_, '>'   , T_IntegralNumber_   ): 'F',
                    (T_NegInfinityNumber_, '>'   , T_NegInfinityNumber_): 'F',
                    (T_NegInfinityNumber_, '>'   , T_PosInfinityNumber_): 'F',
                    (T_NegInfinityNumber_, '&lt;', T_NegInfinityNumber_): 'F',
                    (T_PosInfinityNumber_, '>'   , T_PosInfinityNumber_): 'F',
                    (T_PosInfinityNumber_, '&lt;', T_FiniteNumber_     ): 'F',
                    (T_PosInfinityNumber_, '&lt;', T_IntegralNumber_   ): 'F',
                    (T_PosInfinityNumber_, '&lt;', T_NegInfinityNumber_): 'F',
                    (T_PosInfinityNumber_, '&lt;', T_PosInfinityNumber_): 'F',

                    # true or false:
                    (T_FiniteNumber_           , '>'   , T_FiniteNumber_           ): 'TF',
                    (T_FiniteNumber_           , '>'   , T_IntegralNumber_         ): 'TF',
                    (T_FiniteNumber_           , '&lt;', T_FiniteNumber_           ): 'TF',
                    (T_FiniteNumber_           , '&lt;', T_IntegralNumber_         ): 'TF',
                    (T_IntegralNumber_         , '≥'   , T_IntegralNumber_         ): 'TF',
                    (T_IntegralNumber_         , '>'   , T_IntegralNumber_         ): 'TF',
                    (T_IntegralNumber_         , '='   , T_IntegralNumber_         ): 'TF',
                    (T_NonIntegralFiniteNumber_, '≥'   , T_NonIntegralFiniteNumber_): 'TF',
                    (T_NonIntegralFiniteNumber_, '>'   , T_IntegralNumber_         ): 'TF',
                    (T_NonIntegralFiniteNumber_, '&lt;', T_IntegralNumber_         ): 'TF',
                    (T_NonIntegralFiniteNumber_, '&lt;', T_NonIntegralFiniteNumber_): 'TF',

                    # -------
                    # BigInt:

                    (T_BigInt, '>'   , T_BigInt): 'TF',
                    (T_BigInt, '&lt;', T_BigInt): 'TF',
                    (T_BigInt, '≠'   , T_BigInt): 'TF',

                    # --------
                    # Using the mathematical operator '≠' to compare non-numeric values:
                    #
                    # SetTypedArrayFromTypedArray has:
                    #   1. If _target_.[[ContentType]] ≠ _source_.[[ContentType]], ...
                    # TypedArraySpeciesCreate has:
                    #   1. If _result_.[[ContentType]] ≠ _exemplar_.[[ContentType]], ...
                    # InitializeTypedArrayFromTypedArray has:
                    #   1. If _srcArray_.[[ContentType]] ≠ _O_.[[ContentType]], ...

                    (T_tilde_BigInt_, '≠', T_tilde_Number_): 'TE',
                    (T_tilde_Number_, '≠', T_tilde_BigInt_): 'TE',

                    (T_tilde_BigInt_, '≠', T_tilde_BigInt_): 'FE',
                    (T_tilde_Number_, '≠', T_tilde_Number_): 'FE',

                }[triple]

                env3 = (
                    env2
                    .with_expr_type_narrowed(a, a_memtype)
                    .with_expr_type_narrowed(b, b_memtype)
                )

                if 'T' in something:
                    # There is at least one pair of values
                    # conforming to the given pair of static types
                    # for which the comparison holds (is true).
                    t_envs.append(env3)

                if 'F' in something:
                    # There is at least one pair of values
                    # for which the comparison does not hold (is false).
                    f_envs.append(env3)

                if 'E' in something:
                    # There is at least one pair of values
                    # for which the comparison is ill-defined/non-sensical.
                    add_pass_error(
                        cond,
                        f"comparison has incompatible types: {a_memtype} vs. {b_memtype}"
                    )

        return (envs_or(t_envs), envs_or(f_envs))

    @condd.put(r'{CONDITION_1} : {var} is as small as possible')
    def _(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_MathInteger_)
        return (env0, env0)

# ------------------------------------------------------------------------------
#> This specification denotes most numeric values in base 10;
#> it also uses numeric values of the form 0x followed by digits 0-9 or A-F as base-16 values.

if 1:
    @exprd.put(r"{dec_int_lit} : \b [0-9]+ (?![0-9A-Za-z])")
    def _(expr, env0, _):
        return (T_MathNonNegativeInteger_, env0)

    tbd['{VAL_DESC} : -1'] = a_subset_of(T_MathInteger_)

    tbd['{MATH_LITERAL} : {dec_int_lit}'] = a_subset_of(T_MathInteger_)
    tbd['{MATH_LITERAL} : +&infin;'] = T_MathPosInfinity_
    tbd['{MATH_LITERAL} : -&infin;'] = T_MathNegInfinity_
    tbd['{MATH_LITERAL} : +∞'] = T_MathPosInfinity_
    tbd['{MATH_LITERAL} : -∞'] = T_MathNegInfinity_

    @exprd.put(r"{MATH_LITERAL} : {hex_int_lit}")
    @exprd.put(r"{MATH_LITERAL} : {dec_int_lit}")
    @exprd.put(r"{MATH_LITERAL} : -5")
    @exprd.put(r"{BASE} : 10")
    @exprd.put(r"{BASE} : 2")
    def _(expr, env0, _):
        # [] = expr.children
        return (T_MathInteger_, env0)

    @exprd.put(r"{MATH_LITERAL} : 64 (that is, 8<sup>2</sup>)")
    def _(expr, env0, _):
        [] = expr.children
        return (T_MathInteger_, env0)

    @exprd.put(r"{MATH_LITERAL} : 8.64")
    @exprd.put(r"{MATH_LITERAL} : 0.5")
    def _(expr, env0, _):
        return (T_MathReal_, env0)

    @exprd.put(r"{MATH_LITERAL} : +&infin;")
    @exprd.put(r"{MATH_LITERAL} : +∞")
    def _(expr, env0, _):
        return (T_MathPosInfinity_, env0)

    @exprd.put(r"{MATH_LITERAL} : -&infin;")
    @exprd.put(r"{MATH_LITERAL} : -∞")
    def _(expr, env0, _):
        return (T_MathNegInfinity_, env0)

# ------------------------------------------------------------------------------
#> When the term <dfn>integer</dfn> is used in this specification,
#> it refers to a mathematical value which is in the set of integers,
#> unless otherwise stated.

if 1:
    tbd['{VAL_DESC} : an integer'] = T_MathInteger_
    tbd['{VAL_DESC} : an integer ≥ {dsb_word}'] = a_subset_of(T_MathInteger_)
    tbd['{VAL_DESC} : a non-negative integer that is evenly divisible by 4'] = a_subset_of(T_MathNonNegativeInteger_)
    tbd['{VAL_DESC} : a non-negative integer'] = T_MathNonNegativeInteger_ # currently mapped to MathInteger_
    tbd['{VAL_DESC} : a positive integer'] = a_subset_of(T_MathNonNegativeInteger_)

    @exprd.put(r"{EXPR} : the integer that is {EXPR}")
    def _(expr, env0, _):
        [ex] = expr.children
        env0.assert_expr_is_of_type(ex, T_MathInteger_)
        return (T_MathInteger_, env0)

    @tbd.put('{VAL_DESC} : a non-negative integer less than or equal to {EX}')
    @tbd.put('{VAL_DESC} : a non-negative integer which is ≤ {EXPR}')
    def _(val_desc, env):
        [ex] = val_desc.children
        env.assert_expr_is_of_type(ex, T_MathNonNegativeInteger_)
        return a_subset_of(T_MathNonNegativeInteger_)

# ------------------------------------------------------------------------------
#> When the term <dfn>integral Number</dfn> is used in this specification,
#> it refers to a Number value whose mathematical value is in the set of integers.

if 1:
    tbd['{VAL_DESC} : an integral Number'] = T_IntegralNumber_
    tbd['{VAL_DESC} : an odd integral Number'] = a_subset_of(T_IntegralNumber_)
    tbd['{VAL_DESC} : a non-negative integral Number'] = a_subset_of(T_IntegralNumber_)

# ------------------------------------------------------------------------------
#> The notation “<emu-eqn>_x_ modulo _y_</emu-eqn>”
#> (_y_ must be finite and non-zero)
#> computes a value _k_ of the same sign as _y_ (or zero)
#> such that <emu-eqn>abs(_k_) &lt; abs(_y_) and _x_ - _k_ = _q_ × _y_</emu-eqn>
#> for some integer _q_.

# ------------------------------------------------------------------------------
#> The phrase "the result of <dfn>clamping</dfn> _x_ between _lower_ and _upper_"
#> (where _x_ is an extended mathematical value
#> and _lower_ and _upper_ are mathematical values such that _lower_ ≤ _upper_)
#> produces _lower_ if _x_ &lt; _lower_,
#> produces _upper_ if _x_ > _upper_,
#> and otherwise produces _x_.

if 1:
    @exprd.put(r"{EXPR} : the result of clamping {var} between 0 and {EX}")
    def _(expr, env0, _):
        [var, upper_ex] = expr.children
        env0.assert_expr_is_of_type(upper_ex, T_MathInteger_)
        env0.assert_expr_is_of_type(var, T_MathInteger_ | T_MathPosInfinity_ | T_MathNegInfinity_)
        return (T_MathNonNegativeInteger_, env0)

# ------------------------------------------------------------------------------
#> An <dfn>interval</dfn> from lower bound _a_ to upper bound _b_
#> is a possibly-infinite, possibly-empty set of numeric values of the same numeric type.
#> Each bound will be described as either inclusive or exclusive, but not both.

if 1:
    @exprd.put(r"{INTERVAL} : the inclusive interval from {EX} to {EX}")
    @exprd.put(r"{INTERVAL} : the interval from {EX} (inclusive) to {EX} (exclusive)")
    def _(expr, env0, _):
        [lo, hi] = expr.children
        env0.assert_expr_is_of_type(lo, T_MathInteger_)
        env0.assert_expr_is_of_type(hi, T_MathInteger_)
        return (T_MathInteger_, env0)
        # Should maybe be ListType(T_MathInteger_) or something similar

    @condd.put(r"{CONDITION_1} : {var} is in {INTERVAL}")
    @condd.put(r"{CONDITION_1} : {var} is not in {INTERVAL}")
    def _(cond, env0, asserting):
        [var, interval] = cond.children
        env1 = env0.ensure_expr_is_of_type(var, T_MathInteger_)
        env1.assert_expr_is_of_type(interval, T_MathInteger_)
        return (env1, env1)

    @condd.put(r"{CONDITION_1} : there exists an integer {var} in {INTERVAL} such that {CONDITION_1}")
    def _(cond, env0, asserting):
        [i_var, interval, stcond] = cond.children
        env0.assert_expr_is_of_type(interval, T_MathInteger_)
        env_for_cond = env0.plus_new_entry(i_var, T_MathInteger_)
        return tc_cond(stcond, env_for_cond)

    @condd.put(r"{CONDITION_1} : {SETTABLE} ≠ {SETTABLE} for some integer {var} in {INTERVAL}")
    def _(cond, env0, asserting):
        [seta, setb, let_var, interval] = cond.children
        env0.assert_expr_is_of_type(interval, T_MathInteger_)
        env_for_settables = env0.plus_new_entry(let_var, T_MathInteger_)
        env_for_settables.assert_expr_is_of_type(seta, T_MathInteger_)
        env_for_settables.assert_expr_is_of_type(setb, T_MathInteger_)
        return (env0, env0)

    @tbd.put('{VAL_DESC} : an integer in {INTERVAL}')
    def _(val_desc, env):
        [interval] = val_desc.children
        if env is None:
            if interval.source_text() in [
                'the inclusive interval from 0 to 23',
                'the inclusive interval from 0 to 59',
                'the inclusive interval from 0 to 999',
                'the inclusive interval from 1 to 12',
                'the inclusive interval from 1 to 31',
                'the inclusive interval from 2 to 36',
            ]:
                sup_t = T_MathNonNegativeInteger_
            else:
                assert 0, interval
        else:
            env.assert_expr_is_of_type(interval, T_MathInteger_)
            sup_t = T_MathInteger_
        return a_subset_of(sup_t)

    @nv.put(r"{EACH_THING} : integer {var} in {INTERVAL}")
    def _(each_thing, env0):
        [loop_var, interval] = each_thing.children
        env0.assert_expr_is_of_type(interval, T_MathInteger_)
        return env0.plus_new_entry(loop_var, T_MathInteger_)

# ------------------------------------------------------------------------------
# (The spec should talk about bit strings somewhere.)

if 1:
    @exprd.put(r"{EXPR} : the number of leading 1 bits in {var}")
    def _(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_MathNonNegativeInteger_)
        return (T_MathNonNegativeInteger_, env0)

    @exprd.put(r"{EX} : the integer represented by the 32-bit two's complement bit string {var}")
    def _(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_MathInteger_) # bit string
        return (T_MathInteger_, env0)

    @exprd.put(r'{EXPR} : the byte elements of {var} concatenated and interpreted as a bit string encoding of an unsigned little-endian binary number')
    def _(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_MathInteger_))
        return (T_MathInteger_, env1)

    @exprd.put(r"{EXPR} : the byte elements of {var} concatenated and interpreted as a bit string encoding of a binary little-endian two's complement number of bit length {PRODUCT}")
    def _(expr, env0, _):
        [var, product] = expr.children
        env1 = env0.ensure_expr_is_of_type(product, T_MathInteger_ | T_Number); assert env1 is env0
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_MathInteger_))
        return (T_MathInteger_, env1)

    @exprd.put(r'{EXPR} : the byte elements of {var} concatenated and interpreted as a little-endian bit string encoding of an IEEE 754-2019 binary32 value')
    def _(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_MathInteger_))
        return (T_IEEE_binary32_, env1)

    @exprd.put(r'{EXPR} : the byte elements of {var} concatenated and interpreted as a little-endian bit string encoding of an IEEE 754-2019 binary64 value')
    def _(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_MathInteger_))
        return (T_IEEE_binary64_, env1)

    @exprd.put(r"{EXPR} : the result of applying the bitwise AND operation to {var} and {var}")
    @exprd.put(r"{EXPR} : the result of applying the bitwise exclusive OR (XOR) operation to {var} and {var}")
    @exprd.put(r"{EXPR} : the result of applying the bitwise inclusive OR operation to {var} and {var}")
    def _(expr, env0, _):
        [x, y] = expr.children
        env0.assert_expr_is_of_type(x, T_MathInteger_) # "bit string"
        env0.assert_expr_is_of_type(y, T_MathInteger_) # "bit string"
        return (T_MathInteger_, env0) # "bit string"

    @exprd.put(r"{EXPR} : the 32-bit two's complement bit string representing {EX}")
    def _(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_MathInteger_)
        return (T_MathInteger_, env0) # bit string

    @exprd.put(r'{EXPR} : a List whose elements are the {var}-byte binary encoding of {var}. The bytes are ordered in little endian order')
    @exprd.put(r"{EXPR} : a List whose elements are the {var}-byte binary two's complement encoding of {var}. The bytes are ordered in little endian order")
    def _(expr, env0, _):
        [n_var, v_var] = expr.children
        env0.assert_expr_is_of_type(n_var, T_MathNonNegativeInteger_)
        env0.assert_expr_is_of_type(v_var, T_MathNonNegativeInteger_)
        return (ListType(T_MathInteger_), env0)

# ------------------------------------------------------------------------------
# (Although the spec goes into detail about
# the mappings from string-ish to numeric and numeric to String,
# it also assumes such mappings for simple cases.)

if 1:
    @exprd.put(r"{EX} : the digits of the decimal representation of {var} (in order, with no leading zeroes)")
    def _(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_MathInteger_)
        return (ListType(T_code_unit_), env0)

    @exprd.put(r"{EXPR} : the mathematical value denoted by the result of replacing each significant digit in the decimal representation of {var} after the 20th with a 0 digit")
    @exprd.put(r"{EXPR} : the mathematical value denoted by the result of replacing each significant digit in the decimal representation of {var} after the 20th with a 0 digit and then incrementing it at the 20th position (with carrying as necessary)")
    def _(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_MathReal_)
        return (T_MathReal_, env0)

    @condd.put(r"{CONDITION_1} : the decimal representation of {var} has 20 or fewer significant digits")
    def _(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_MathReal_)
        return (env0, env0)

    @exprd.put(r"{EXPR} : the String representation of {EX}, formatted as a decimal number")
    @exprd.put(r"{EXPR} : the String representation of {EX}, formatted as a lowercase hexadecimal number")
    @exprd.put(r"{EXPR} : the String representation of {EX}, formatted as an uppercase hexadecimal number")
    def _(expr, env0, _):
        [ex] = expr.children
        env1 = env0.ensure_expr_is_of_type(ex, T_Number | T_MathInteger_)
        return (T_String, env1)

# ==============================================================================
#@ 5.2.6 Value Notation

#> Values which are internal to the specification
#> and not directly observable from ECMAScript code
#> are indicated with a ~sans-serif~ typeface.

if 1:
    @tbd.put('{LITERAL} : {tilded_word}')
    def _(literal, env):
        [tilded_word] = literal.children
        return type_for_tilded_word(tilded_word)

    @exprd.put(r"{LITERAL} : {tilded_word}")
    def _(expr, env0, _):
        [tilded_word] = expr.children
        return (type_for_tilded_word(tilded_word), env0)

def type_for_tilded_word(tilded_word):
    assert tilded_word.prod.lhs_s == '{tilded_word}'
    [chars] = tilded_word.children
    assert chars[0] == '~'
    assert chars[-1] == '~'
    uchars = chars[1:-1].replace('-', '_').replace('+', '_')
    return NamedType(f"tilde_{uchars}_")

# ==============================================================================
#@ 5.2.7 Identity

#> In this specification,
#> the word “is” is used to compare two values through equality,
#> as in “If _bool_ is *true*, then”.

# (So I'm putting all the "X is Y" forms here.)

if 1:
    @condd.put(r'{CONDITION_1} : {EX} is {var}')
    @condd.put(r"{CONDITION_1} : {EX} is the same value as {EX}")
    def _(cond, env0, asserting):
        [a_ex, b_ex] = cond.children
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

    @condd.put(r"{CONDITION_1} : {EX} is different from {EX}")
    @condd.put(r"{CONDITION_1} : {EX} is the same as {EX}")
    @condd.put(r"{CONDITION_1} : {var} is not the same as {var}")
    @condd.put(r"{CONDITION_1} : {EX} is not the same value as {var}")
    @condd.put(r"{CONDITION_1} : {EX} is {PREFIX_PAREN}")
    def _(cond, env0, asserting):
        [exa, exb] = cond.children
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

    @condd.put(r"{CONDITION_1} : {EX} and {EX} are distinct values")
    def _(cond, env0, asserting):
        [exa, exb] = cond.children
        (exa_type, env1) = tc_expr(exa, env0)
        (exb_type, env2) = tc_expr(exb, env1)
        return (env2, env2)

# ------

    @condd.put(r"{CONDITION_1} : both {EX} and {EX} are {LITERAL}")
    def _(cond, env0, asserting):
        [exa, exb, lit] = cond.children
        (t, env1) = tc_expr(lit, env0); assert env1 is env0
        env1.assert_expr_is_of_type(exa, t)
        env1.assert_expr_is_of_type(exb, t)
        return (env1, env1)

    @condd.put(r'{CONDITION_1} : {EX} and {EX} are both {LITERAL}')
    def _(cond, env0, asserting):
        [exa, exb, lit] = cond.children
        (lit_type, lit_env) = tc_expr(lit, env0); assert lit_env is env0
        if lit_type in [T_Undefined, T_NaN_Number_, T_tilde_accessor_]:
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

    @condd.put(r'{CONDITION_1} : {EX} and {EX} are both {LITERAL} or both {LITERAL}')
    def _(cond, env0, asserting):
        # occurs once, in SameValueNonNumber
        [exa, exb, litc, litd] = cond.children
        assert litc.source_text() == '*true*'
        assert litd.source_text() == '*false*'
        enva = env0.ensure_expr_is_of_type(exa, T_Boolean); assert enva is env0
        envb = env0.ensure_expr_is_of_type(exb, T_Boolean); # assert envb is env0
        return (envb, envb)

    @condd.put(r"{CONDITION_1} : {var} or {var} is {LITERAL}")
    def _(cond, env0, asserting):
        [v1, v2, lit] = cond.children
        env0.assert_expr_is_of_type(v1, T_Number|T_BigInt)
        env0.assert_expr_is_of_type(v2, T_Number|T_BigInt)
        env0.assert_expr_is_of_type(lit, T_Number)
        return (env0, env0)

# ------

    @condd.put(r"{CONDITION_1} : {var} is either a String, Number, Boolean, Null, or an Object that is defined by either an {nonterminal} or an {nonterminal}")
    def _(cond, env0, asserting):
        [var, nonta, nontb] = cond.children
        return env0.with_type_test(var, 'is a', T_String | T_Number | T_Boolean | T_Null | T_Object, asserting)

    @condd.put(r"{CONDITION_1} : {EX} is also {VAL_DESC}")
    @condd.put(r"{CONDITION_1} : {EX} is never {VAL_DESC}")
    @condd.put(r"{CONDITION_1} : {EX} is not {VALUE_DESCRIPTION}")
    @condd.put(r"{CONDITION_1} : {EX} is {VALUE_DESCRIPTION}")
    def _(cond, env0, asserting):
        [ex, vd] = cond.children

        # kludgey?
        r = is_simple_call(ex)
        if r:
            assert cond.prod.rhs_s == r"{EX} is {VALUE_DESCRIPTION}"

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
                if vd.source_text() == '*true*':
                    copula = 'is a'
                elif vd.source_text() == '*false*':
                    copula = 'isnt a'
                else:
                    assert 0
                #
                return env0.with_type_test(var, copula, t, asserting)

        if 'not' in cond.prod.rhs_s or 'never' in cond.prod.rhs_s:
            copula = 'isnt a'
        else:
            copula = 'is a'

        # special handling for Completion Records' [[Type]] field:
        while True: # ONCE
            dotting = ex.is_a('{DOTTING}')
            if dotting is None: break
            (lhs, dsbn) = dotting.children
            dsbn_name = dsbn.source_text()[2:-2]
            if dsbn_name != 'Type': break
            t = type_corresponding_to_comptype_literal(vd)
            return env0.with_type_test(lhs, copula, t, asserting)

        (sub_t, sup_t) = type_bracket_for(vd, env0)
        return env0.with_type_test(ex, copula, [sub_t, sup_t], asserting)

    @condd.put(r"{CONDITION_1} : {EX} is neither {VAL_DESC} nor {VAL_DESC} nor {VAL_DESC}")
    @condd.put(r"{CONDITION_1} : {EX} is neither {VAL_DESC} nor {VAL_DESC}")
    def _(cond, env0, asserting):
        [ex, *vds] = cond.children

        sub_t = T_0
        sup_t = T_0
        for vd in vds:
            (x_sub_t, x_sup_t) = type_bracket_for(vd, env0)
            sub_t |= x_sub_t
            sup_t |= x_sup_t

        return env0.with_type_test(ex, 'isnt a', [sub_t, sup_t], asserting)

    # -------

    @tbd.put('{VALUE_DESCRIPTION} : any of {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, or {VAL_DESC}')
    @tbd.put('{VALUE_DESCRIPTION} : either {VAL_DESC} or {VAL_DESC}')
    @tbd.put('{VALUE_DESCRIPTION} : either {VAL_DESC}, or {VAL_DESC}')
    @tbd.put('{VALUE_DESCRIPTION} : either {VAL_DESC}, {VAL_DESC}, or {VAL_DESC}')
    @tbd.put('{VALUE_DESCRIPTION} : either {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, or {VAL_DESC}')
    @tbd.put('{VALUE_DESCRIPTION} : one of {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, or {VAL_DESC}')
    @tbd.put('{VALUE_DESCRIPTION} : one of {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC} or {VAL_DESC}')
    @tbd.put('{VALUE_DESCRIPTION} : one of {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, or {VAL_DESC}')
    @tbd.put('{VALUE_DESCRIPTION} : one of: {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, or {VAL_DESC}')
    @tbd.put('{VALUE_DESCRIPTION} : {VAL_DESC} or {VAL_DESC}')
    @tbd.put('{VALUE_DESCRIPTION} : {VAL_DESC}, {VAL_DESC}, or {VAL_DESC}')
    @tbd.put('{VALUE_DESCRIPTION} : {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, or {VAL_DESC}')
    @tbd.put('{VALUE_DESCRIPTION} : {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, or {VAL_DESC}')
    @tbd.put('{VALUE_DESCRIPTION} : {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, or {VAL_DESC}')
    @tbd.put('{VALUE_DESCRIPTION} : {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, or {VAL_DESC}')
    @tbd.put('{VALUE_DESCRIPTION} : {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, or {VAL_DESC}')
    def _(value_description, env):
        result_sub_t = T_0
        result_sup_t = T_0
        for val_desc in value_description.children:
            (sub_t, sup_t) = type_bracket_for(val_desc, env)
            result_sub_t |= sub_t
            result_sup_t |= sup_t
        return (result_sub_t, result_sup_t)

    @tbd.put('{VALUE_DESCRIPTION} : {VAL_DESC}, but not {VALUE_DESCRIPTION}')
    def _(value_description, env):
        # [pos_desc, neg_desc] = value_description.children
        # t = type_bracket_for(pos_desc) - type_bracket_for(neg_desc)
        vd_st = value_description.source_text()
        if vd_st == 'an ECMAScript language value, but not a Number':
            return T_Undefined | T_Null | T_Boolean | T_BigInt | T_String | T_Symbol | T_Object
        elif vd_st == 'an ECMAScript language value, but not *undefined* or *null*':
            return T_Boolean | T_Number | T_BigInt | T_String | T_Symbol | T_Object
        elif vd_st == 'an ECMAScript language value, but not a TypedArray':
            return a_subset_of(T_Tangible_)
        elif vd_st == 'a Number, but not *NaN*':
            return T_FiniteNumber_ | T_NegInfinityNumber_ | T_PosInfinityNumber_
        elif vd_st == 'an Object, but not a TypedArray or an ArrayBuffer':
            return a_subset_of(T_Object)
        else:
            assert 0, vd_st

    @tbd.put('{VAL_DESC} : a {h_emu_xref}')
    def _(val_desc, env):
        [emu_xref] = val_desc.children
        # polymorphic
        if emu_xref.source_text() in [
            '<emu-xref href="#leading-surrogate"></emu-xref>',
            '<emu-xref href="#trailing-surrogate"></emu-xref>',
        ]:
            return a_subset_of(T_code_unit_)
        elif emu_xref.source_text() == '<emu-xref href="#sec-built-in-function-objects">built-in function object</emu-xref>':
            return a_subset_of(T_function_object_)
        else:
            assert 0, emu_xref

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 6 ECMAScript Data Types and Values

#> Within this specification,
#> the notation “Type(_x_)” is used as shorthand for
#> “the <em>type</em> of _x_”
#> where “type” refers to the ECMAScript language and specification types
#> defined in this clause.

if 1:
    @condd.put(r'{TYPE_TEST} : Type({TYPE_ARG}) is the same as Type({TYPE_ARG})')
    @condd.put(r'{TYPE_TEST} : Type({TYPE_ARG}) is different from Type({TYPE_ARG})')
    def _(cond, env0, asserting):
        # Env can't represent the effect of these.
        # If the incoming static types were different,
        # the 'true' env could at least narrow those to their intersection,
        # but the form only appears twice, and in both cases the static types are the same.
        return (env0, env0)

    @condd.put(r"{TYPE_TEST} : Type({TYPE_ARG}) is not an element of {var}")
    def _(cond, env0, asserting):
        # once, in CreateListFromArrayLike
        [type_arg, var] = cond.children
        env0.assert_expr_is_of_type(var, ListType(T_LangTypeName_))
        return (env0, env0)

    @exprd.put(r"{LITERAL} : {TYPE_NAME}")
    def _(expr, env0, _):
        [type_name] = expr.children
        return (T_LangTypeName_, env0)

    tbd['{VAL_DESC} : anything'] = T_host_defined_

# ==============================================================================
#@ 6.1 ECMAScript Language Types

if 1:
    tbd['{VAL_DESC} : an ECMAScript language value'] = T_Tangible_
    tbd['{LIST_ELEMENTS_DESCRIPTION} : ECMAScript language values'] = T_Tangible_
    tbd['{LIST_ELEMENTS_DESCRIPTION} : names of ECMAScript Language Types'] = T_LangTypeName_

# ==============================================================================
#@ 6.1.1 The Undefined Type

if 1:
    @exprd.put(r'{LITERAL} : *undefined*')
    def _(expr, env0, _):
        return (T_Undefined, env0)

    tbd['{LITERAL} : *undefined*'] = T_Undefined

# ==============================================================================
#@ 6.1.2 The Null Type

if 1:
    @exprd.put(r'{LITERAL} : *null*')
    def _(expr, env0, _):
        return (T_Null, env0)

    tbd['{LITERAL} : *null*'] = T_Null

    tbd['{LITERAL} : the value *null*'] = T_Null

# ==============================================================================
#@ 6.1.3 The Boolean Type

if 1:
    tbd['{VAL_DESC} : a Boolean'] = T_Boolean

    tbd['{LITERAL} : {BOOL_LITERAL}'] = a_subset_of(T_Boolean)

    @exprd.put(r"{LITERAL} : {BOOL_LITERAL}")
    def _(expr, env0, _):
        return (T_Boolean, env0)

# ==============================================================================
#@ 6.1.4 The String Type

# ------------------------------------------------------------------------------
#> The <dfn>String type</dfn> is the set of all ordered sequences
#> of zero or more 16-bit unsigned integer values (“elements”)
#> up to a maximum length of 2<sup>53</sup> - 1 elements.
#> The String type is generally used to represent textual data in a running ECMAScript program,
#> in which case each element in the String is treated as a UTF-16 code unit value.

if 1:
    tbd['{VAL_DESC} : a String'] = T_String
    tbd['{LITERAL} : {STR_LITERAL}'] = a_subset_of(T_String)
    tbd['{VAL_DESC} : the String value {STR_LITERAL}'] = a_subset_of(T_String)
    tbd['{LIST_ELEMENTS_DESCRIPTION} : Strings'] = T_String
    tbd['{LIST_ELEMENTS_DESCRIPTION} : either Strings or *null*'     ] = T_String | T_Null
    tbd['{LIST_ELEMENTS_DESCRIPTION} : either Strings or *undefined*'] = T_String | T_Undefined

    @exprd.put(r'{LITERAL} : {STR_LITERAL}')
    def _(expr, env0, _):
        return (T_String, env0)

    @exprd.put(r'{STR_LITERAL} : *","* (a comma)')
    @exprd.put(r'{STR_LITERAL} : the empty String')
    @exprd.put(r'{STR_LITERAL} : {starred_str}')
    @exprd.put(r'{STR_LITERAL} : {starred_str} ({code_unit_lit} followed by {code_unit_lit})')
    def _(expr, env0, _):
        return (T_String, env0)

    @exprd.put(r"{EX} : the String {var}")
    @exprd.put(r"{EXPR} : the String value {SETTABLE}")
    def _(expr, env0, _):
        [ex] = expr.children
        env0.ensure_expr_is_of_type(ex, T_String)
        return (T_String, env0)

    @exprd.put("{EX} : {h_code_quote}")
    def _(expr, env0, _):
        [h_code_quote] = expr.children
        return (T_String, env0)

    @exprd.put(r"{EXPR} : {var}'s single code unit element") # todo: element of String
    def _(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_String)
        return (T_code_unit_, env1)

    @exprd.put(r'{EX} : the first code unit of {var}')
    def _(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_String)
        return (T_code_unit_, env1)

# ----

    @condd.put(r'{CONDITION_1} : {var} does not consist of a single code unit')
    def _(cond, env0, asserting):
        [var] = cond.children
        env1 = env0.ensure_expr_is_of_type(var, T_String)
        return (env1, env1)

    @condd.put(r'{CONDITION_1} : {var} contains any code unit other than *"d"*, *"g"*, *"i"*, *"m"*, *"s"*, *"u"*, or *"y"* or if it contains the same code unit more than once')
    def _(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_String)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {var} contains a code unit that is not a radix-{var} digit")
    def _(cond, env0, asserting):
        [svar, rvar] = cond.children
        env0.assert_expr_is_of_type(svar, T_String)
        env0.assert_expr_is_of_type(rvar, T_MathInteger_)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {var} starts with {STR_LITERAL}")
    def _(cond, env0, asserting):
        [var, str_literal] = cond.children
        env0.assert_expr_is_of_type(var, T_String)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {var} starts with {STR_LITERAL} followed by {EX} or more decimal digits")
    def _(cond, env0, asserting):
        [var, str_literal, ex] = cond.children
        env0.assert_expr_is_of_type(var, T_String)
        env0.assert_expr_is_of_type(ex, T_MathNonNegativeInteger_)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : the first two code units of {var} are either {STR_LITERAL} or {STR_LITERAL}")
    def _(cond, env0, asserting):
        [var, lita, litb] = cond.children
        env0.assert_expr_is_of_type(var, T_String)
        env0.assert_expr_is_of_type(lita, T_String)
        env0.assert_expr_is_of_type(litb, T_String)
        return (env0, env0)

    @condd.put(r'{CONDITION_1} : {var} is the same sequence of code units as {var}')
    def _(cond, env0, asserting):
        [var1, var2] = cond.children
        env0.assert_expr_is_of_type(var1, T_String)
        env0.ensure_expr_is_of_type(var2, T_String)
        return (env0, env0)

    @condd.put(r'{CONDITION_1} : {var} and {var} are exactly the same sequence of code units (same length and same code units at corresponding indices)')
    def _(cond, env0, asserting):
        # occurs once, in SameValueNonNumber
        [vara, varb] = cond.children
        enva = env0.ensure_expr_is_of_type(vara, T_String); assert enva is env0
        envb = env0.ensure_expr_is_of_type(varb, T_String); # assert envb is env0
        return (envb, envb)

    @condd.put(r"{CONDITION_1} : {NAMED_OPERATION_INVOCATION} is: {starred_str}, {starred_str}, {starred_str}, {starred_str}, {starred_str}, {starred_str}, {starred_str}, {starred_str}, or {starred_str}")
    def _(cond, env0, asserting):
        [noi, *ss_] = cond.children
        env0.assert_expr_is_of_type(noi, T_String)
        return (env0, env0)

# ------------------------------------------------------------------------------
#> Each element is regarded as occupying a position within the sequence.
#> These positions are indexed with non-negative integers.
#> The first element (if any) is at index 0, the next element (if any) at index 1, and so on.

    @exprd.put(r"{EX} : the code unit at index {EX} within {EX}")
    def _(expr, env0, _):
        [index_ex, str_ex] = expr.children
        env0.assert_expr_is_of_type(str_ex, T_String)
        env1 = env0.ensure_expr_is_of_type(index_ex, T_MathInteger_)
        return (T_code_unit_, env1)

    @exprd.put(r"{EXPR} : the index within {var} of the first such code unit")
    def _(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_String)
        return (T_MathNonNegativeInteger_, env0)

    @exprd.put(r"{EXPR} : the 8-bit value represented by the two hexadecimal digits at index {EX} and {EX}")
    def _(expr, env0, _):
        [posa, posb] = expr.children
        env0.assert_expr_is_of_type(posa, T_MathInteger_)
        env0.assert_expr_is_of_type(posb, T_MathInteger_)
        return (T_MathInteger_, env0)

    @condd.put(r"{CONDITION_1} : the code units at index ({SUM}) and ({SUM}) within {var} do not represent hexadecimal digits")
    def _(cond, env0, asserting):
        [posa, posb, var] = cond.children
        env0.assert_expr_is_of_type(posa, T_MathInteger_)
        env0.assert_expr_is_of_type(posb, T_MathInteger_)
        env0.assert_expr_is_of_type(var, T_String)
        return (env0, env0)

# ------------------------------------------------------------------------------
#> The length of a String is the number of elements (i.e., 16-bit values) within it.
#> The empty String has length zero and therefore contains no elements.

    @exprd.put(r"{NUM_COMPARAND} : the length of {var}")
    @exprd.put(r"{EX} : the length of {var}")
    def _(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_String)
        return (T_MathNonNegativeInteger_, env1)

# ------------------------------------------------------------------------------
#> In this specification,
#> the phrase "the <dfn>string-concatenation</dfn> of _A_, _B_, ..."
#> (where each argument is a String value, a code unit, or a sequence of code units)
#> denotes the String value whose sequence of code units
#> is the concatenation of the code units (in order) of each of the arguments (in order).

    @exprd.put(r"{MULTILINE_EXPR} : the string-concatenation of:{I_BULLETS}")
    def _(expr, env0, _):
        [bullets] = expr.children
        # Should check the bullets
        return (T_String, env0)

    @exprd.put(r"{EXPR} : the string-concatenation of {EX} and {EX}")
    @exprd.put(r"{EXPR} : the string-concatenation of {EX}, {EX}, and {EX}")
    @exprd.put(r"{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, and {EX}")
    @exprd.put(r"{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, {EX}, and {EX}")
    @exprd.put(r"{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, {EX}, {EX}, and {EX}")
    @exprd.put(r"{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, and {EX}")
    @exprd.put(r"{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, and {EX}")
    @exprd.put(r"{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, and {EX}")
    @exprd.put(r"{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, and {EX}")
    @exprd.put(r"{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, and {EX}")
    def _(expr, env0, _):
        env1 = env0
        for ex in expr.children:
            env1 = env1.ensure_expr_is_of_type(ex, T_String | T_code_unit_ | ListType(T_code_unit_))
        return (T_String, env1)

# ------------------------------------------------------------------------------
#> The phrase "the <dfn>substring</dfn> of _S_ from _inclusiveStart_ to _exclusiveEnd_"
#> (where _S_ is a String value or a sequence of code units and _inclusiveStart_ and _exclusiveEnd_ are integers)
#> denotes the String value consisting of
#> the consecutive code units of _S_
#> beginning at index _inclusiveStart_ and ending immediately before index _exclusiveEnd_
#> (which is the empty String when _inclusiveStart_ = _exclusiveEnd_).
#> If the "to" suffix is omitted, the length of _S_ is used as the value of _exclusiveEnd_.

    @exprd.put(r"{EX} : the substring of {var} from {EX} to {EX}")
    def _(expr, env0, _):
        [s_var, start_var, end_var] = expr.children
        env0.assert_expr_is_of_type(s_var, T_String)
        env1 = env0.ensure_expr_is_of_type(start_var, T_MathNonNegativeInteger_)
        env2 = env1.ensure_expr_is_of_type(end_var, T_MathNonNegativeInteger_)
        return (T_String, env2)

    @exprd.put(r"{EX} : the substring of {var} from index {dec_int_lit}")
    @exprd.put(r"{EX} : the substring of {var} from {EX}")
    def _(expr, env0, _):
        [s_var, start_var] = expr.children
        env0.assert_expr_is_of_type(s_var, T_String)
        env0.ensure_expr_is_of_type(start_var, T_MathNonNegativeInteger_)
        return (T_String, env0)

# ------------------------------------------------------------------------------
#> The phrase "<dfn>the ASCII word characters</dfn>"
#> denotes the following String value,
#> which consists solely of every letter and number in the Unicode Basic Latin block
#> along with U+005F (LOW LINE):
#> *"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789_"*.
#> For historical reasons, it has significance to various algorithms.

    @exprd.put(r'{STR_LITERAL} : the ASCII word characters')
    def _(expr, env0, _):
        return (T_String, env0)

# ------------------------------------------------------------------------------
# Other ways to specify a String value:

    @exprd.put(r"{EX} : the first {SUM} code units of {var}")
    def _(expr, env0, _):
        [summ, var] = expr.children
        env0.assert_expr_is_of_type(var, T_String)
        env1 = env0.ensure_expr_is_of_type(summ, T_MathInteger_)
        return (T_String, env1)

    @exprd.put(r"{EX} : the remaining {EX} code units of {var}")
    @exprd.put(r"{EXPR} : the other {EX} code units of {var}")
    def _(expr, env0, _):
        [ex, var] = expr.children
        env0.assert_expr_is_of_type(var, T_String)
        env1 = env0.ensure_expr_is_of_type(ex, T_MathInteger_)
        return (T_String, env1)

    @exprd.put(r"{EXPR} : the String value consisting solely of {code_unit_lit}")
    @exprd.put(r"{EXPR} : the String value containing only the code unit {var}")
    @exprd.put(r"{EXPR} : the String value containing the single code unit {var}")
    def _(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_code_unit_)
        return (T_String, env1)

    @exprd.put(r"{EXPR} : the String value consisting of {EX}")
    def _(expr, env0, _):
        [ex] = expr.children
        env1 = env0.ensure_expr_is_of_type(ex, T_code_unit_ | ListType(T_code_unit_))
        return (T_String, env1)

    @exprd.put(r"{EXPR} : the String value that is a copy of {var} with both leading and trailing white space removed")
    @exprd.put(r"{EXPR} : the String value that is a copy of {var} with leading white space removed")
    @exprd.put(r"{EXPR} : the String value that is a copy of {var} with trailing white space removed")
    def _(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_String)
        return (T_String, env0)

    @exprd.put(r"{EXPR} : the String value that is the same as {var} except that each occurrence of {code_unit_lit} in {var} has been replaced with the six code unit sequence {STR_LITERAL}")
    def _(expr, env0, _):
        [var, lita, var2, litb] = expr.children
        assert var.children == var2.children
        env1 = env0.ensure_expr_is_of_type(var, T_String)
        return (T_String, env1)

    @exprd.put(r"{EXPR} : the String value that is the result of normalizing {var} into the normalization form named by {var} as specified in {h_a}")
    def _(expr, env0, _):
        [s_var, nf_var, h_a] = expr.children
        env0.assert_expr_is_of_type(s_var, T_String)
        env0.assert_expr_is_of_type(nf_var, T_String)
        return (T_String, env0)

    @exprd.put(r"{EXPR} : the String value containing {var} occurrences of {code_unit_lit}")
    def _(expr, env0, _):
        [n, lit] = expr.children
        env0.assert_expr_is_of_type(lit, T_code_unit_)
        return (T_String, env0)

    @exprd.put(r"{EXPR} : the String value that is made from {var} copies of {var} appended together")
    def _(expr, env0, _):
        [n_var, s_var] = expr.children
        env0.assert_expr_is_of_type(s_var, T_String)
        env1 = env0.ensure_expr_is_of_type(n_var, T_MathInteger_)
        return (T_String, env1)

    @exprd.put(r"{EXPR} : the String value consisting of repeated concatenations of {EX} truncated to length {var}")
    def _(expr, env0, _):
        [ex, var] = expr.children
        env0.assert_expr_is_of_type(ex, T_String)
        env1 = env0.ensure_expr_is_of_type(var, T_MathInteger_)
        return (T_String, env1)

    @exprd.put(r"{EXPR} : the String value formed by concatenating all the element Strings of {var} with each adjacent pair of Strings separated with {code_unit_lit}. A comma is not inserted either before the first String or after the last String")
    def _(expr, env0, _):
        [var, str_literal] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_String))
        return (T_String, env1)

    @exprd.put(r"{EXPR} : the String value formed by concatenating all the element Strings of {var} with each adjacent pair of Strings separated with {var}. The {var} String is not inserted either before the first String or after the last String")
    def _(expr, env0, _):
        [var, sep_var, sep_var2] = expr.children
        assert sep_var.children == sep_var2.children
        env0.assert_expr_is_of_type(sep_var, T_String)
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_String))
        return (T_String, env1)

    @exprd.put(r"{EXPR} : the String value whose code units are the elements in the List {var}. If {var} has no elements, the empty String is returned")
    def _(expr, env0, _):
        [list_var, list_var2] = expr.children
        assert same_source_text(list_var, list_var2)
        env0.assert_expr_is_of_type(list_var, ListType(T_code_unit_))
        return (T_String, env0)

    @exprd.put(r"{EXPR} : the implementation-defined list-separator String value appropriate for the host environment's current locale (such as {STR_LITERAL})")
    def _(expr, env0, _):
        [str_lit] = expr.children
        return (T_String, env0)

# ------------------------------------------------------------------------------
# Going from a String value to some other type of value:

    @exprd.put(r"{EXPR} : a List whose elements are the code units that are the elements of {var}")
    @exprd.put(r"{EXPR} : a List consisting of the sequence of code units that are the elements of {var}")
    def _(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_String)
        return (ListType(T_code_unit_), env0)

    @exprd.put(r"{EXPR} : the result of interpreting each of {var}'s 16-bit elements as a Unicode BMP code point. UTF-16 decoding is not applied to the elements")
    def _(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_String)
        return (T_Unicode_code_points_, env0)

    @exprd.put(r"{EXPR} : the sequence of code points resulting from interpreting each of the 16-bit elements of {var} as a Unicode BMP code point. UTF-16 decoding is not applied to the elements")
    def _(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_String)
        return (T_Unicode_code_points_, env0)

    @exprd.put(r"{EXPR} : the integer value that is represented by {var} in radix-{var} notation, using the letters <b>A</b>-<b>Z</b> and <b>a</b>-<b>z</b> for digits with values 10 through 35")
    def _(expr, env0, _):
        [zvar, rvar] = expr.children
        env0.assert_expr_is_of_type(zvar, T_String)
        env0.assert_expr_is_of_type(rvar, T_MathInteger_)
        return (T_MathInteger_, env0)

# ------------------------------------------------------------------------------
# Comparing a String value to a nonterminal:

    # for 19.2.4 parseFloat
    @condd.put(r"{CONDITION_1} : neither {var} nor any prefix of {var} satisfies the syntax of a {nonterminal} (see {h_emu_xref})")
    def _(cond, env0, asserting):
        [var1, var2, nont, emu_xref] = cond.children
        assert same_source_text(var1, var2)
        env0.assert_expr_is_of_type(var1, T_String)
        return (env0, env0)

    # for 19.2.4 parseFloat
    @exprd.put(r"{EXPR} : the longest prefix of {var}, which might be {var} itself, that satisfies the syntax of a {nonterminal}")
    def _(expr, env0, _):
        [var1, var2, nont] = expr.children
        assert same_source_text(var1, var2)
        env0.assert_expr_is_of_type(var1, T_String)
        return (T_String, env0)

    # for B.2.1.2
    @condd.put(r"{CONDITION_1} : {var} can be interpreted as an expansion of {nonterminal}")
    def _(cond, env0, asserting):
        [var, nont] = cond.children
        env0.assert_expr_is_of_type(var, T_String)
        return (env0, env0)

# ==============================================================================
#@ 6.1.5 The Symbol Type

if 1:
    tbd['{VAL_DESC} : a Symbol'] = T_Symbol

    @condd.put(r'{CONDITION_1} : {var} and {var} are both the same Symbol value')
    def _(cond, env0, asserting):
        # occurs once, in SameValueNonNumber
        [vara, varb] = cond.children
        enva = env0.ensure_expr_is_of_type(vara, T_Symbol); assert enva is env0
        envb = env0.ensure_expr_is_of_type(varb, T_Symbol); # assert envb is env0
        return (envb, envb)

# ----

    @exprd.put(r"{LITERAL} : {atat_word}")
    def _(expr, env0, _):
        return (T_Symbol, env0)

#> Each Symbol value immutably holds
#> an associated value called [[Description]]
#> that is either *undefined* or a String value.

    @exprd.put(r"{EXPR} : a new unique Symbol value whose {DSBN} value is {var}")
    def _(expr, env0, _):
        [dsbn, var] = expr.children
        assert dsbn.source_text() == '[[Description]]'
        env0.assert_expr_is_of_type(var, T_String | T_Undefined)
        return (T_Symbol, env0)

    @exprd.put(r"{EXPR} : {var}'s {DSBN} value")
    def _(expr, env0, _):
        [var, dsbn] = expr.children
        env0.assert_expr_is_of_type(var, T_Symbol)
        assert dsbn.source_text() == '[[Description]]'
        return (T_String | T_Undefined, env0)

# ==============================================================================
#@ 6.1.6 Numeric Types

# ==============================================================================
#@ 6.1.6.1 The Number Type

if 1:
    tbd['{VAL_DESC} : a Number'] = T_Number

    tbd['{NUMBER_LITERAL} : {starred_nan_lit}'] = T_NaN_Number_
    tbd['{NUMBER_LITERAL} : {starred_neg_infinity_lit}{h_sub_fancy_f}'] = T_NegInfinityNumber_
    tbd['{NUMBER_LITERAL} : {starred_pos_infinity_lit}{h_sub_fancy_f}'] = T_PosInfinityNumber_
    tbd['{NUMBER_LITERAL} : {starred_int_lit}{h_sub_fancy_f}'] = a_subset_of(T_IntegralNumber_)

    @condd.put(r'{CONDITION_1} : {var} is the same Number value as {var}')
    def _(cond, env0, asserting):
        [var1, var2] = cond.children
        env0.assert_expr_is_of_type(var1, T_Number)
        env1 = env0.ensure_expr_is_of_type(var2, T_Number)
        return (env1, env1)

    @condd.put(r'{CONDITION_1} : {var} and {var} are the same Number value')
    def _(cond, env0, asserting):
        # in Abstract Relational Comparison
        [vara, varb] = cond.children
        enva = env0.ensure_expr_is_of_type(vara, T_Number); # assert enva is env0
        envb = enva.ensure_expr_is_of_type(varb, T_Number); # assert envb is env0
        return (envb, envb)

    @condd.put(r"{CONDITION_1} : {var} is finite")
    def _(cond, env0, asserting):
        [var] = cond.children
        (t, env1) = tc_expr(var, env0); assert env1 is env0
        if t.is_a_subtype_of_or_equal_to(T_Number):
            return env1.with_type_test(var, 'is a', T_FiniteNumber_, asserting)
        elif t.is_a_subtype_of_or_equal_to(T_ExtendedMathReal_):
            return env1.with_type_test(var, 'is a', T_MathReal_, asserting)
        else:
            assert 0

    @condd.put(r"{CONDITION_1} : {var} and {var} are both finite")
    def _(cond, env0, asserting):
        [a, b] = cond.children
        (a_t_env, a_f_env) = env0.with_type_test(a, 'is a', T_FiniteNumber_, asserting)
        (b_t_env, b_f_env) = env0.with_type_test(b, 'is a', T_FiniteNumber_, asserting)
        return (
            env_and(a_t_env, b_t_env),
            env_or(a_f_env, b_f_env)
        )

    @condd.put(r"{CONDITION_1} : {var} and {var} are finite and non-zero")
    def _(cond, env0, asserting):
        [avar, bvar] = cond.children
        env0.assert_expr_is_of_type(avar, T_Number)
        env0.assert_expr_is_of_type(bvar, T_Number)
        return (
            env0
                .with_expr_type_narrowed(avar, T_FiniteNumber_)
                .with_expr_type_narrowed(bvar, T_FiniteNumber_),
            env0
        )

    @condd.put(r"{CONDITION_1} : {var} is not finite")
    def _(cond, env0, asserting):
        [var] = cond.children
        (t, env1) = tc_expr(var, env0); assert env1 is env0
        if t.is_a_subtype_of_or_equal_to(T_Number | T_BigInt):
            return env1.with_type_test(var, 'isnt a', T_FiniteNumber_, asserting)
        elif t.is_a_subtype_of_or_equal_to(T_ExtendedMathReal_):
            return env1.with_type_test(var, 'isnt a', T_MathReal_, asserting)
        else:
            assert 0

    @condd.put(r"{CONDITION_1} : {var} is finite and is neither {NUMBER_LITERAL} nor {NUMBER_LITERAL}")
    def _(cond, env0, asserting):
        [var, lita, litb] = cond.children
        env1 = env0.ensure_expr_is_of_type(var, T_FiniteNumber_)
        env1.assert_expr_is_of_type(lita, T_FiniteNumber_)
        env1.assert_expr_is_of_type(litb, T_FiniteNumber_)
        return (env1, env1)

    @exprd.put(r"{NUMBER_LITERAL} : {starred_neg_infinity_lit}{h_sub_fancy_f}")
    def _(expr, env0, _):
        return (T_NegInfinityNumber_, env0)

    @exprd.put(r"{NUMBER_LITERAL} : {starred_pos_infinity_lit}{h_sub_fancy_f}")
    def _(expr, env0, _):
        return (T_PosInfinityNumber_, env0)

    @exprd.put(r"{NUMBER_LITERAL} : {starred_nan_lit}")
    @exprd.put(r'{NUMBER_LITERAL} : the *NaN* Number value')
    def _(expr, env0, _):
        return (T_NaN_Number_, env0)

    @exprd.put(r"{NUMBER_LITERAL} : *0.5*{h_sub_fancy_f}")
    @exprd.put(r"{NUMBER_LITERAL} : *-0.5*{h_sub_fancy_f}")
    def _(expr, env0, _):
        return (T_NonIntegralFiniteNumber_, env0)

    @exprd.put(r"{NUMBER_LITERAL} : {starred_int_lit}{h_sub_fancy_f}")
    def _(expr, env0, _):
        [_, _] = expr.children
        return (T_IntegralNumber_, env0)

    @exprd.put(r'{EXPR} : the Number value that corresponds to {var}')
    def _(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_IEEE_binary32_ | T_IEEE_binary64_ | T_MathInteger_)
        return (T_Number, env1)

    @exprd.put(r"{EX} : the Number value for {EX}")
    def _(expr, env0, _):
        [ex] = expr.children
        (ex_type, env1) = tc_expr(ex, env0)
        # env1 = env0.ensure_expr_is_of_type(ex, T_MathReal_)
        if ex_type.is_a_subtype_of_or_equal_to(T_MathInteger_):
            return (T_IntegralNumber_, env1)
        elif ex_type.is_a_subtype_of_or_equal_to(T_MathInteger_ | T_MathPosInfinity_ | T_MathNegInfinity_):
            return (T_IntegralNumber_ | T_NegInfinityNumber_ | T_PosInfinityNumber_, env1)
        elif ex_type.is_a_subtype_of_or_equal_to(T_ExtendedMathReal_):
            return (T_Number, env1)
        else:
            add_pass_error(
                ex,
                f"expected MathReal, got {ex_type}"
            )
            return (T_Number, env1)

    @exprd.put(r"{EXPR} : the result of negating {var}; that is, compute a Number with the same magnitude but opposite sign")
    def _(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_Number)
        return (T_Number, env0)

    @exprd.put(r"{EXPR} : the smallest (closest to -∞) integral Number value that is not less than {var}")
    @exprd.put(r"{EXPR} : the greatest (closest to +∞) integral Number value that is not greater than {var}")
    @exprd.put(r"{EXPR} : the integral Number closest to {var}, preferring the Number closer to +∞ in the case of a tie")
    def _(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_Number)
        return (T_Number, env0)

    @exprd.put(r"{EXPR} : the integral Number nearest {var} in the direction of *+0*{h_sub_fancy_f}")
    def _(expr, env0, _):
        [var, _] = expr.children
        env0.assert_expr_is_of_type(var, T_Number)
        return (T_Number, env0)

    @exprd.put(r"{EXPR} : an implementation-approximated Number value representing {EXPR}")
    def _(expr, env0, _):
        [ex] = expr.children
        env0.assert_expr_is_of_type(ex, T_MathReal_)
        return (T_Number, env0)

    @exprd.put(r"{EXPR} : the result of converting {var} to a value in IEEE 754-2019 binary32 format using roundTiesToEven mode")
    @exprd.put(r"{EXPR} : the result of converting {var} to a value in IEEE 754-2019 binary64 format")
    @exprd.put(r"{EXPR} : the ECMAScript Number value corresponding to {var}")
    def _(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_Number)
        # XXX The intermediates are not really T_Number
        return (T_Number, env0)

    @exprd.put(r'{EXPR} : a List whose elements are the 4 bytes that are the result of converting {var} to IEEE 754-2019 binary32 format using roundTiesToEven mode. The bytes are arranged in little endian order. If {var} is *NaN*, {var} may be set to any implementation chosen IEEE 754-2019 binary32 format Not-a-Number encoding. An implementation must always choose the same encoding for each implementation distinguishable *NaN* value')
    @exprd.put(r'{EXPR} : a List whose elements are the 8 bytes that are the IEEE 754-2019 binary64 format encoding of {var}. The bytes are arranged in little endian order. If {var} is *NaN*, {var} may be set to any implementation chosen IEEE 754-2019 binary64 format Not-a-Number encoding. An implementation must always choose the same encoding for each implementation distinguishable *NaN* value')
    def _(expr, env0, _):
        var = expr.children[0]
        env1 = env0.ensure_expr_is_of_type(var, T_Number)
        return (ListType(T_MathInteger_), env1)

# Treating an integral Number like a bit-string:

    @exprd.put(r"{EXPR} : the result of applying bitwise complement to {var}. The mathematical value of the result is exactly representable as a 32-bit two's complement bit string")
    def _(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_IntegralNumber_)
        return (T_IntegralNumber_, env0)

    @exprd.put(r"{EX} : the result of left shifting {var} by {var} bits. The mathematical value of the result is exactly representable as a 32-bit two's complement bit string")
    @exprd.put(r"{EXPR} : the result of performing a sign-extending right shift of {var} by {var} bits. The most significant bit is propagated. The mathematical value of the result is exactly representable as a 32-bit two's complement bit string")
    @exprd.put(r"{EXPR} : the result of performing a zero-filling right shift of {var} by {var} bits. Vacated bits are filled with zero. The mathematical value of the result is exactly representable as a 32-bit unsigned bit string")
    def _(expr, env0, _):
        [avar, bvar] = expr.children
        env1 = env0.ensure_expr_is_of_type(avar, T_IntegralNumber_)
        env1.assert_expr_is_of_type(bvar, T_MathInteger_)
        return (T_IntegralNumber_, env1)

    @exprd.put(r"{EXPR} : the number of leading zero bits in the unsigned 32-bit binary representation of {var}")
    def _(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_IntegralNumber_)
        return (T_MathNonNegativeInteger_, env0)

# ------------------------------------------------------------------------------

tbd['{VAL_DESC} : an IEEE 754-2019 binary32 NaN value'] = a_subset_of(T_IEEE_binary32_)
tbd['{VAL_DESC} : an IEEE 754-2019 binary64 NaN value'] = a_subset_of(T_IEEE_binary64_)

# ==============================================================================
#@ 6.1.6.2 The BigInt Type

if 1:
    tbd['{VAL_DESC} : a BigInt'] = T_BigInt
    tbd['{LIST_ELEMENTS_DESCRIPTION} : BigInts'] = T_BigInt
    tbd['{LITERAL} : {BIGINT_LITERAL}'] = a_subset_of(T_BigInt)

# ----

    @exprd.put(r"{BIGINT_LITERAL} : {starred_int_lit}{h_sub_fancy_z}")
    def _(expr, env0, _):
        [_, _] = expr.children
        return (T_BigInt, env0)

    @exprd.put(r"{EXPR} : the BigInt value that represents {EX}")
    def _(expr, env0, _):
        [ex] = expr.children
        env0.assert_expr_is_of_type(ex, T_MathReal_|T_BigInt)
        return (T_BigInt, env0)

    @exprd.put(r"{EXPR} : the BigInt value that corresponds to {var}")
    def _(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_MathInteger_)
        return (T_BigInt, env0)

    @exprd.put(r"{EX} : the BigInt value for {EX}")
    def _(expr, env0, _):
        [ex] = expr.children
        env0.assert_expr_is_of_type(ex, T_MathInteger_)
        return (T_BigInt, env0)

    @exprd.put(r"{EX} : the sum of {var} and {var}")
    @exprd.put(r"{EX} : the product of {var} and {var}")
    @exprd.put(r"{EX} : the difference {var} minus {var}")
    def _(expr, env0, _):
        [x, y] = expr.children
        env0.assert_expr_is_of_type(x, T_BigInt)
        env0.assert_expr_is_of_type(y, T_BigInt)
        return (T_BigInt, env0)

    @exprd.put(r"{EXPR} : the String value consisting of the representation of {var} using radix {var}")
    def _(expr, env0, _):
        [x_var, radix_var] = expr.children
        env0.assert_expr_is_of_type(x_var, T_BigInt)
        env0.assert_expr_is_of_type(radix_var, T_MathInteger_)
        return (T_String, env0)

# ==============================================================================
#@ 6.1.7 The Object Type

#> An Object is logically a collection of properties.
#> Each property is either a data property, or an accessor property:
#>  -- A <dfn>data property</dfn> associates a key value with
#>     an ECMAScript language value and a set of Boolean attributes.
#>  -- An <dfn>accessor property</dfn> associates a key value with
#>     one or two accessor functions, and a set of Boolean attributes.
#>     The accessor functions are used to store or retrieve
#>     an ECMAScript language value that is associated with the property.

#> Properties are identified using key values.
#> A <dfn>property key</dfn> value is either an ECMAScript String value or a Symbol value.
#> All String and Symbol values, including the empty String, are valid as property keys.
#> A <dfn>property name</dfn> is a property key that is a String value.

if 1:
    tbd['{VAL_DESC} : an Object'] = T_Object
    tbd['{VAL_DESC} : an extensible object that does not have a {starred_str} own property'] = a_subset_of(T_Object)
    tbd['{VAL_DESC} : a property key'] = T_String | T_Symbol
    tbd['{LIST_ELEMENTS_DESCRIPTION} : Objects'                            ] = T_Object
    tbd['{LIST_ELEMENTS_DESCRIPTION} : property keys'                      ] = T_String | T_Symbol

    @tbd.put('{VAL_DESC} : an? {PROPERTY_KIND} property')
    def _(val_desc, env):
        [kind] = val_desc.children
        t = {
            'accessor': T_accessor_property_,
            'data'    : T_data_property_,
        }[kind.source_text()]
        return t

    @condd.put(r'{CONDITION_1} : {var} and {var} are the same Object value')
    def _(cond, env0, asserting):
        # in SameValueNonNumber
        [vara, varb] = cond.children
        enva = env0.ensure_expr_is_of_type(vara, T_Object); # assert enva is env0
        envb = enva.ensure_expr_is_of_type(varb, T_Object); # assert envb is env0
        return (envb, envb)

    @condd.put(r'{CONDITION_1} : {var} does not have an own property with key {var}')
    @condd.put(r"{CONDITION_1} : {var} does not currently have a property {var}")
    def _(cond, env0, asserting):
        [obj_var, key_var] = cond.children
        env0.assert_expr_is_of_type(obj_var, T_Object)
        env0.assert_expr_is_of_type(key_var, T_String | T_Symbol)
        return (env0, env0)

    @condd.put(r'''{CONDITION_1} : The mathematical value of {var}'s {starred_str} property is {EX}''')
    def _(cond, env0, asserting):
        [var, prop_name, ex] = cond.children
        env0.assert_expr_is_of_type(var, T_Object)
        env0.assert_expr_is_of_type(ex, T_MathInteger_)
        return (env0, env0)

    @nv.put(r"{EACH_THING} : own property key {var} of {var} that is an array index, whose numeric value is greater than or equal to {var}, in descending numeric index order")
    def _(each_thing, env0):
        [loop_var, obj_var, lo_var] = each_thing.children
        env0.assert_expr_is_of_type(obj_var, T_Object)
        env0.assert_expr_is_of_type(lo_var, T_Number)
        return env0.plus_new_entry(loop_var, T_String)

    @nv.put(r"{EACH_THING} : own property key {var} of {var} such that {CONDITION}, in ascending numeric index order")
    @nv.put(r"{EACH_THING} : own property key {var} of {var} such that {CONDITION}, in ascending chronological order of property creation")
    def _(each_thing, env0):
        [loop_var, obj_var, condition] = each_thing.children
        env0.assert_expr_is_of_type(obj_var, T_Object)
        env1 = env0.plus_new_entry(loop_var, T_String | T_Symbol)
        (tenv, fenv) = tc_cond(condition, env1)
        return tenv

    @nv.put(r'{COMMAND} : Create own properties of {var} corresponding to the definitions in {h_emu_xref}.')
    def _(anode, env0):
        [var, emu_xref] = anode.children
        env0.assert_expr_is_of_type(var, T_Object)
        return env0

    @nv.put(r"{COMMAND} : Remove the own property with name {var} from {var}.")
    def _(anode, env0):
        [name_var, obj_var] = anode.children
        env0.assert_expr_is_of_type(name_var, T_String | T_Symbol)
        env0.assert_expr_is_of_type(obj_var, T_Object)
        return env0

    @exprd.put(r"{EXPR} : {var}'s own property whose key is {var}")
    def _(expr, env0, _):
        [obj_var, key_var] = expr.children
        env0.assert_expr_is_of_type(obj_var, T_Object)
        env0.assert_expr_is_of_type(key_var, T_String | T_Symbol)
        return (T_property_, env0)

    @exprd.put(r"{EXPR} : the String value of the property name")
    def _(expr, env0, _):
        # property of the Global Object
        # todo: make that explicit
        [] = expr.children
        return (T_String, env0)

    @exprd.put(r"{EXPR} : such an object created in a host-defined manner")
    def _(expr, env0, _):
        [] = expr.children
        return (T_Object, env0)

#> An <dfn>integer index</dfn>
#> is a String-valued property key
#> that is a canonical numeric string
#> and whose numeric value is either *+0*<sub>𝔽</sub> or a positive integral Number ≤ 𝔽(2<sup>53</sup> - 1).

    tbd['{VAL_DESC} : an integer index'] = a_subset_of(T_String)

#> An <dfn>array index</dfn>
#> is an integer index whose numeric value _i_
#> is in the range <emu-eqn>*+0*<sub>𝔽</sub> ≤ _i_ &lt; 𝔽(2<sup>32</sup> - 1)</emu-eqn>.

    tbd['{VAL_DESC} : an array index'] = a_subset_of(T_String)

# ==============================================================================
#@ 6.1.7.1 Property Attributes

if 1:
    @nv.put(r"{COMMAND} : Create an own {PROPERTY_KIND} property named {var} of object {var} whose {dsb_word}, {dsb_word}, {dsb_word}, and {dsb_word} attributes are set to the value of the corresponding field in {var} if {var} has that field, or to the attribute's {h_emu_xref} otherwise.")
    def _(anode, env0):
        [kind, name_var, obj_var, *dsbw_, desc_var, desc_var2, emu_xref] = anode.children
        assert desc_var.source_text() == desc_var2.source_text()
        env0.ensure_expr_is_of_type(name_var, T_String | T_Symbol)
        env0.assert_expr_is_of_type(obj_var, T_Object)
        env0.assert_expr_is_of_type(desc_var, T_Property_Descriptor)
        return env0

    @nv.put(r"{SMALL_COMMAND} : set the corresponding attribute of the property named {var} of object {var} to the value of the field")
    def _(anode, env0):
        [name_var, obj_var] = anode.children
        env0.ensure_expr_is_of_type(name_var, T_String | T_Symbol)
        env0.assert_expr_is_of_type(obj_var, T_Object)
        return env0

    @nv.put(r"{COMMAND} : Replace the property named {var} of object {var} with an? {PROPERTY_KIND} property whose {dsb_word} and {dsb_word} attributes are set to {var} and {var}, respectively, and whose {dsb_word} and {dsb_word} attributes are set to the value of the corresponding field in {var} if {var} has that field, or to the attribute's {h_emu_xref} otherwise.")
    def _(anode, env0):
        [name_var, obj_var, kind, dsbw1, dsbw2, field_var1, field_var2, dsbw3, dsbw4, desc_var, desc_var2, emu_xref] = anode.children
        assert desc_var.source_text() == desc_var2.source_text()
        env0.ensure_expr_is_of_type(name_var, T_String | T_Symbol)
        env0.assert_expr_is_of_type(obj_var, T_Object)
        env0.assert_expr_is_of_type(desc_var, T_Property_Descriptor)
        return env0

    @exprd.put(r"{SETTABLE} : {var}'s {DSBN} attribute")
    def _(expr, env0, _):
        [prop_var, dsbn] = expr.children
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

    @exprd.put(r'{EXPR} : an Iterator object ({h_emu_xref}) whose `next` method iterates over all the String-valued keys of enumerable properties of {var}. The iterator object is never directly accessible to ECMAScript code. The mechanics and order of enumerating the properties is not specified but must conform to the rules specified below')
    def _(expr, env0, _):
        [emu_xref, var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_Object)
        return (T_Iterator_object_, env1)

# ==============================================================================
#@ 6.1.7.2 Object Internal Methods and Internal Slots

#> The actual semantics of objects, in ECMAScript, are specified via
#> algorithms called <em>internal methods</em>.
#> Each object in an ECMAScript engine is associated with
#> a set of internal methods that defines its runtime behaviour

if 1:
    @condd.put(r'{CONDITION_1} : {var} has an? {DSBN} internal method')
    def _(cond, env0, asserting):
        [var, dsbn] = cond.children
        env1 = env0.ensure_expr_is_of_type(var, T_Object)
        dsbn_name = dsbn.source_text()[2:-2]
        if dsbn_name == 'Call':
            # one of the few where the presence/absence of an internal method is a type-test?
            return env1.with_type_test(var, 'is a', T_function_object_, asserting)
        elif dsbn_name == 'Construct':
            return env1.with_type_test(var, 'is a', T_constructor_object_, asserting)
        else:
            assert 0, dsbn_name

#> Internal slots correspond to internal state
#> that is associated with objects
#> and used by various ECMAScript specification algorithms.

if 1:
    tbd['{VAL_DESC} : an internal slot name'] = T_SlotName_
    tbd['{LIST_ELEMENTS_DESCRIPTION} : internal slot names'    ] = T_SlotName_
    tbd['{LIST_ELEMENTS_DESCRIPTION} : names of internal slots'] = T_SlotName_

    @exprd.put(r"{EX} : {DSBN}")
    def _(expr, env0, _):
        [dsbn] = expr.children
        return (T_SlotName_, env0)

    tbd['{VAL_DESC} : an Object that has a {dsb_word} internal slot'] = a_subset_of(T_Object)

    @condd.put(r'{CONDITION_1} : {var} has an? {DSBN} internal slot')
    @condd.put(r'{CONDITION_1} : {var} also has a {DSBN} internal slot')
    def _(cond, env0, asserting):
        [var, dsbn] = cond.children
        env1 = env0.ensure_expr_is_of_type(var, T_Object)
        # Whether or not it has that particular slot, it's still an Object.
        # XXX we could be more specific about the sub-kind of Object
        return (env1, env1)

    @condd.put(r"{CONDITION_1} : {var} has {DSBN} and {DSBN} internal slots")
    def _(cond, env0, asserting):
        # XXX could be a type-test
        [var, *dsbn_] = cond.children
        env0.assert_expr_is_of_type(var, T_Object)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {var} has an? {DSBN} or {DSBN} internal slot")
    def _(cond, env0, asserting):
        [var, dsbna, dsbnb] = cond.children
        env0.assert_expr_is_of_type(var, T_Object)
        assert dsbna.source_text() == '[[StringData]]'
        assert dsbnb.source_text() == '[[NumberData]]'
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {var} has an? {DSBN} internal slot whose value is an Object")
    def _(cond, env0, asserting):
        [var, dsbn] = cond.children
        env0.assert_expr_is_of_type(var, T_Object) # more specific?
        return (env0, env0)

    @condd.put(r'{CONDITION_1} : {var} does not have an? {DSBN} internal slot')
    def _(cond, env0, asserting):
        [var, dsbn] = cond.children
        env1 = env0.ensure_expr_is_of_type(var, T_Object)
        # Whether or not it has that particular slot, it's still an Object.
        # XXX The particular DSBN could have a (sub-)type-constraining effect
        return (env1, env1)

    @condd.put(r"{CONDITION_1} : {var} does not have an? {var} internal slot")
    def _(cond, env0, asserting):
        [obj_var, slotname_var] = cond.children
        env0.assert_expr_is_of_type(obj_var, T_Object)
        env0.assert_expr_is_of_type(slotname_var, T_SlotName_)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {var} does not have either a {DSBN} or an {DSBN} internal slot")
    def _(cond, env0, asserting):
        [var, dsbna, dsbnb] = cond.children
        env0.assert_expr_is_of_type(var, T_Object)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {var} has all of the internal slots of a For-In Iterator Instance ({h_emu_xref})")
    def _(cond, env0, asserting):
        [var, emu_xref] = cond.children
        env0.assert_expr_is_of_type(var, T_Object)
        return (env0, env0)

    # explicit-exotics:
    @exprd.put(r"{EX} : the internal slots listed in {h_emu_xref}")
    def _(expr, env0, _):
        # XXX really, the *names* of the internal slots...
        return (ListType(T_SlotName_), env0)

#> All objects have an internal slot named [[PrivateElements]],
#> which is a List of PrivateElements.
#> This List represents the values of
#> the private fields, methods, and accessors for the object.
#> Initially, it is an empty List.

set_up_internal_thing('slot', 'PrivateElements', ListType(T_PrivateElement))

#> Internal methods and internal slots are identified within this specification
#> using names enclosed in double square brackets [[ ]].

#> <emu-xref href="#table-essential-internal-methods"></emu-xref>
#> summarizes the <em>essential internal methods</em>
#> used by this specification
#> that are applicable to all objects created or manipulated by ECMAScript code.
#> Every object must have algorithms for all of the essential internal methods.
#> However, all objects do not necessarily use the same algorithms for those methods.

if 1:
    @nv.put(r"{COMMAND} : Set {var}'s essential internal methods to the definitions specified in {h_emu_xref}.")
    @nv.put(r"{COMMAND} : Set {var}'s essential internal methods to the default ordinary object definitions specified in {h_emu_xref}.")
    def _(anode, env0):
        [var, emu_xref] = anode.children
        env1 = env0.ensure_expr_is_of_type(var, T_Object)
        return env1

    @nv.put(r"{COMMAND} : Set {var}'s essential internal methods, except for {DSBN} and {DSBN}, to the definitions specified in {h_emu_xref}.")
    def _(anode, env0):
        var = anode.children[0]
        env0.assert_expr_is_of_type(var, T_Object)
        return env0

    # explicit-exotics:
    @condd.put(r"{CONDITION_1} : the caller will not be overriding both {var}'s {DSBN} and {DSBN} essential internal methods")
    @condd.put(r"{CONDITION_1} : the caller will not be overriding all of {var}'s {DSBN}, {DSBN}, and {DSBN} essential internal methods")
    def _(cond, env0, asserting):
        var = cond.children[0]
        env0.assert_expr_is_of_type(var, T_Object)
        return (env0, env0)

#> An <dfn>ordinary object</dfn> is an object that satisfies all of the following criteria:
#>  -- For the internal methods listed in <emu-xref href="#table-essential-internal-methods"></emu-xref>,
#>     the object uses those defined in
#>     <emu-xref href="#sec-ordinary-object-internal-methods-and-internal-slots"></emu-xref>.
#>  -- If the object has a [[Call]] internal method,
#>     it uses either the one defined in
#>     <emu-xref href="#sec-ecmascript-function-objects-call-thisargument-argumentslist"></emu-xref>
#>     or the one defined in
#>     <emu-xref href="#sec-built-in-function-objects-call-thisargument-argumentslist"></emu-xref>.
#>  -- If the object has a [[Construct]] internal method,
#>     it uses either the one defined in
#>     <emu-xref href="#sec-ecmascript-function-objects-construct-argumentslist-newtarget"></emu-xref>
#>     or the one defined in
#>     <emu-xref href="#sec-built-in-function-objects-construct-argumentslist-newtarget"></emu-xref>.

if 1:
    tbd['{VAL_DESC} : an ordinary object'] = a_subset_of(T_Object)
    tbd['{VAL_DESC} : an ordinary, extensible object with no non-configurable properties'] = a_subset_of(T_Object)
    tbd['{VAL_DESC} : an extensible ordinary object with no own properties'] = a_subset_of(T_Object)

    @condd.put(r"{CONDITION_1} : {DOTTING} is not the ordinary object internal method defined in {h_emu_xref}")
    def _(cond, env0, asserting):
        [dotting, emu_xref] = cond.children
        env0.assert_expr_is_of_type(dotting, T_proc_)
        return (env0, env0)

#> An <dfn>exotic object</dfn> is an object that is not an ordinary object.

#> A <dfn>function object</dfn> is an object that supports the [[Call]] internal method.
#> A <dfn>constructor</dfn> is an object that supports the [[Construct]] internal method.

    tbd['{VAL_DESC} : a function object'] = T_function_object_
    tbd['{VAL_DESC} : a constructor'] = T_constructor_object_
    tbd['{VAL_DESC} : a callable Object'] = T_function_object_

# ------

# Creating objects:

if 1:
    @exprd.put(r'{EXPR} : a newly created object with an internal slot for each name in {var}')
    def _(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_SlotName_))
        return (T_Object, env1)

    @exprd.put(r'{EXPR} : a new built-in function object that, when called, performs the action described by {var} using the provided arguments as the values of the corresponding parameters specified by {var}. The new function object has internal slots whose names are the elements of {var}, and an {DSBN} internal slot')
    def _(expr, env0, _):
        [var1, var2, var3, dsbn] = expr.children
        env1 = env0.ensure_expr_is_of_type(var1, T_proc_ | T_alg_steps)
        # env1 = env0.ensure_expr_is_of_type(var2, )
        return (T_function_object_, env1)

    @exprd.put(r"{EXPR} : a new {cap_word} object whose {dsb_word} internal slot is set to {var}. See {h_emu_xref} for a description of {cap_word} objects")
    def _(expr, env0, _):
        [cap_word, dsb_word, var, emu_xref, cap_word2] = expr.children
        T = cap_word.source_text()
        assert T in ['Boolean', 'Number', 'String', 'Symbol', 'BigInt']
        assert dsb_word.source_text() == f"[[{T}Data]]"
        assert var.source_text() == '_argument_'
        assert cap_word2.source_text() == T
        return (T_Object, env0)

# ==============================================================================
#@ 6.1.7.4 Well-Known Intrinsic Objects

#> Within this specification
#> a reference such as %name% means
#> the intrinsic object, associated with the current realm, corresponding to the name.

if 1:
    @exprd.put(r"{LITERAL} : {percent_word}")
    def _(expr, env0, _):
        [percent_word] = expr.children
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

    @exprd.put(r"{EXPR} : the intrinsic function {percent_word}")
    def _(expr, env0, _):
        [percent_word] = expr.children
        return (T_function_object_, env0)

    @exprd.put(r"{EXPR} : {var}'s intrinsic object named {var}")
    def _(expr, env0, _):
        [r_var, n_var] = expr.children
        env0.assert_expr_is_of_type(r_var, T_Realm_Record)
        env0.assert_expr_is_of_type(n_var, T_String)
        return (T_Object, env0)

    # 10.1.{13,14}
    @condd.put(r"{CONDITION_1} : {var} is this specification's name of an intrinsic object. The corresponding object must be an intrinsic that is intended to be used as the {DSBN} value of an object")
    def _(cond, env0, asserting):
        [var, dsbn] = cond.children
        env0.assert_expr_is_of_type(var, T_String)
        return (env0, env0)

# ==============================================================================
#@ 6.2 ECMAScript Specification Types

# ==============================================================================
#@ 6.2.2 The List and Record Specification Types

# ------------------------------------------------------------------------------
# List:

if 1:
    tbd['{VAL_DESC} : a possibly empty List'] = T_List

    @tbd.put('{VAL_DESC} : a List of {LIST_ELEMENTS_DESCRIPTION}')
    def _(val_desc, env):
        [led] = val_desc.children
        (sub_t, sup_t) = type_bracket_for(led, env)
        return (ListType(sub_t), ListType(sup_t))

    @tbd.put('{VAL_DESC} : a List of {LIST_ELEMENTS_DESCRIPTION} with length equal to {EX}')
    def _(val_desc, env):
        [led, ex] = val_desc.children
        env.assert_expr_is_of_type(ex, T_MathInteger_)
        (led_sub_t, led_sup_t) = type_bracket_for(led, env)
        return a_subset_of(ListType(led_sup_t))
        # inexact because of length restriction 

    @tbd.put('{VAL_DESC} : a non-empty List of {LIST_ELEMENTS_DESCRIPTION}')
    def _(val_desc, env):
        [led] = val_desc.children
        (led_sub_t, led_sup_t) = type_bracket_for(led, env)
        return a_subset_of(ListType(led_sup_t))
        # inexact because of 'non-empty'

    tbd['{VAL_DESC} : a List of a single Number'] = a_subset_of(ListType(T_Number))
    tbd['{VAL_DESC} : a possibly empty List, each of whose elements is a String or *undefined*'] = ListType(T_String | T_Undefined)

# ------------------------------------------------------------------------------
# make a List:

if 1:
    @exprd.put(r"{EX} : « »")
    def _(expr, env0, _):
        [] = expr.children
        return (T_List, env0)

    @exprd.put(r"{EX} : « {EXLIST} »")
    def _(expr, env0, _):
        [exlist] = expr.children
        ex_types = set()
        for ex in exes_in_exlist(exlist):
            (ex_type, env1) = tc_expr(ex, env0); assert env1 is env0
            ex_types.add(ex_type)
        element_type = union_of_types(ex_types)
        list_type = ListType(element_type)
        return (list_type, env0)

    @exprd.put(r'{EXPR} : a new empty List')
    def _(expr, env0, _):
        [] = expr.children
        return (T_List, env0) # (ListType(T_0), env0)

    @exprd.put(r"{EXPR} : a List whose sole element is {EX}")
    def _(expr, env0, _):
        [element_expr] = expr.children
        (element_type, env1) = tc_expr(element_expr, env0); assert env1.equals(env0)
        return (ListType(element_type), env0)

    @exprd.put(r"{EXPR} : a copy of the List {var}")
    @exprd.put(r"{EXPR} : a List whose elements are the elements of {var}")
    def _(expr, env0, _):
        [var] = expr.children
        t = env0.assert_expr_is_of_type(var, T_List)
        return (t, env0)

    @exprd.put(r"{EXPR} : the list-concatenation of {EX} and {EX}")
    def _(expr, env0, _):
        [var, noi] = expr.children
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

    @exprd.put(r"{EXPR} : the list-concatenation of {EX}, {EX}, and {EX}")
    def _(expr, env0, _):
        [exa, exb, exc] = expr.children
        # kludge
        if exa.source_text() == '_names1_':
            et = T_String
        elif exa.source_text() == '_declarations1_':
            et = T_Parse_Node
        elif exa.source_text() == '« _matched_ »':
            et = T_String | T_IntegralNumber_
        else:
            assert 0, exa
        lt = ListType(et)
        env1 = env0.ensure_expr_is_of_type(exa, lt)
        env2 = env1.ensure_expr_is_of_type(exb, lt)
        env3 = env2.ensure_expr_is_of_type(exc, lt)
        return (lt, env3)

    @exprd.put(r'{EXPR} : a List whose elements are the elements of {var} ordered as if an Array of the same values had been sorted using {percent_word} using {LITERAL} as {var}')
    def _(expr, env0, _):
        [var, _, _, _] = expr.children
        (t, env1) = tc_expr(var, env0); assert env1 is env0
        assert t.is_a_subtype_of_or_equal_to(T_List)
        return (t, env0)

    @exprd.put(r'{EXPR} : a List whose elements are the first {var} elements of {var}')
    def _(expr, env0, _):
        [nvar, listvar] = expr.children
        env0.assert_expr_is_of_type(nvar, T_MathNonNegativeInteger_)
        (t, env1) = tc_expr(listvar, env0); assert env1 is env0
        assert t.is_a_subtype_of_or_equal_to(T_List)
        return (t, env0)

    @exprd.put(r"{EX} : {EX} occurrences of {code_unit_lit}")
    def _(expr, env0, _):
        [ex, cu_lit] = expr.children
        env1 = env0.ensure_expr_is_of_type(ex, T_MathInteger_)
        env0.assert_expr_is_of_type(cu_lit, T_code_unit_)
        return (ListType(T_code_unit_), env1)

    @exprd.put(r"{EXPR} : the List of {nonterminal} items in {PROD_REF}, in source text order")
    def _(expr, env0, _):
        [nont, prod_ref] = expr.children
        return (ListType(T_Parse_Node), env0)

    @exprd.put(r"{EXPR} : a List of {EX} {LITERAL} values, indexed 1 through {EX}")
    def _(expr, env0, _):
        [var, literal, var2] = expr.children
        assert var.source_text() == var2.source_text()
        env0.assert_expr_is_of_type(var, T_MathInteger_)
        (lit_t, env1) = tc_expr(literal, env0); assert env1 is env0
        return (ListType(lit_t), env1)

    @exprd.put(r"{EXPR} : the List that is {DOTTING}")
    def _(expr, env0, _):
        [dotting] = expr.children
        (dotting_type, env1) = tc_expr(dotting, env0); assert env1 is env0
        dotting_type.is_a_subtype_of_or_equal_to(T_List)
        return (dotting_type, env0)

# ------------------------------------------------------------------------------
# modify a List:

    @nv.put(r"{COMMAND} : Append {EX} as an element of {var}.")
    @nv.put(r"{COMMAND} : Append {EX} to the end of {EX}.")
    @nv.put(r"{COMMAND} : Append {EX} to {EX}.")
    @nv.put(r"{COMMAND} : Insert {var} as the first element of {var}.")
    @nv.put(r"{COMMAND} : Prepend {var} to {var}.")
    @nv.put(r"{SMALL_COMMAND} : append {EX} to {SETTABLE}")
    def _(anode, env0):
        [value_ex, list_ex] = anode.children
        return env0.ensure_A_can_be_element_of_list_B(value_ex, list_ex)

    @nv.put(r"{COMMAND} : Append the pair (a two element List) consisting of {var} and {var} to the end of {var}.")
    def _(anode, env0):
        [avar, bvar, list_var] = anode.children
        env0.assert_expr_is_of_type(avar, T_String | T_Symbol)
        env0.assert_expr_is_of_type(bvar, T_Property_Descriptor)
        (list_type, env1) = tc_expr(list_var, env0); assert env1 is env0
        assert list_type == T_List
        return env0.with_expr_type_narrowed(list_var, ListType(ListType(T_TBD)))

    @nv.put(r"{COMMAND} : Append to {var} the elements of {var}.")
    def _(anode, env0):
        [lista, listb] = anode.children
        env0.assert_expr_is_of_type(lista, ListType(T_SlotName_))
        env0.assert_expr_is_of_type(listb, ListType(T_SlotName_))
        return env0

    @nv.put(r'{COMMAND} : Append to {var} each element of {var} that is not already an element of {var}.')
    def _(anode, env0):
        [vara, varb, varc] = anode.children
        (vara_type, enva) = tc_expr(vara, env0); assert enva is env0
        (varb_type, envb) = tc_expr(varb, env0); assert envb is env0
        (varc_type, envc) = tc_expr(varc, env0); assert envc is env0
        if vara_type == T_TBD and varb_type == T_TBD and varc_type == T_TBD:
            pass
        else:
            assert vara_type.is_a_subtype_of_or_equal_to(T_List)
            assert vara_type == varb_type
            assert varb_type == varc_type
        return env0

    @nv.put(r"{COMMAND} : Remove {var} from {var}.")
    @nv.put(r"{COMMAND} : Remove {var} from {DOTTING}.")
    def _(anode, env0):
        [item_var, list_ex] = anode.children
        list_type = env0.assert_expr_is_of_type(list_ex, T_List)
        env0.assert_expr_is_of_type(item_var, list_type.element_type)
        return env0

    @nv.put(r"{COMMAND} : Remove the first element from {var}.")
    def _(anode, env0):
        [var] = anode.children
        env0.assert_expr_is_of_type(var, T_List)
        return env0

    @nv.put(r"{COMMAND} : Remove the first {var} elements of {var}.")
    def _(anode, env0):
        [nvar, listvar] = anode.children
        env0.assert_expr_is_of_type(nvar, T_MathNonNegativeInteger_)
        env0.assert_expr_is_of_type(listvar, T_List)
        return env0

    @nv.put(r"{COMMAND} : Remove the last element of {SETTABLE}.")
    def _(anode, env0):
        [settable] = anode.children
        env0.assert_expr_is_of_type(settable, T_List)
        return env0

    @nv.put(r"{SMALL_COMMAND} : remove that element from the {var}")
    def _(anode, env0):
        [var] = anode.children
        env0.assert_expr_is_of_type(var, T_List)
        return env0

    @nv.put(r"{COMMAND} : Replace {var} in {var} with {var}.")
    def _(anode, env0):
        [ex_var, list_var, rep_var] = anode.children
        env0.assert_expr_is_of_type(list_var, ListType(T_PrivateElement))
        env0.assert_expr_is_of_type(ex_var, T_PrivateElement)
        env0.assert_expr_is_of_type(rep_var, T_PrivateElement)
        return env0

    @nv.put(r"{COMMAND} : Replace the element of {SETTABLE} whose value is {var} with an element whose value is {LITERAL}.")
    def _(anode, env0):
        [list_var, elem_ex, lit] = anode.children
        env1 = env0.ensure_A_can_be_element_of_list_B(elem_ex, list_var)
        env2 = env1.ensure_A_can_be_element_of_list_B(lit, list_var)
        return env2

    @nv.put(r'{SMALL_COMMAND} : reverse the order of the elements of {var}')
    def _(anode, env0):
        [var] = anode.children
        return env0.ensure_expr_is_of_type(var, T_List)

# ------------------------------------------------------------------------------
# iterate over a List:

    @nv.put(r"{EACH_THING} : element {var} of {EX}")
    @nv.put(r"{EACH_THING} : element {var} of {var}, in reverse List order")
    def _(each_thing, env0):
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
        return env1.plus_new_entry(loop_var, element_type)

# ------------------------------------------------------------------------------
# ask questions about a List:

    @condd.put(r'{CONDITION_1} : {EX} is empty')
    @condd.put(r"{CONDITION_1} : {var} is not empty")
    def _(cond, env0, asserting):
        [var] = cond.children
        # polymorphic
        env0.assert_expr_is_of_type(var, T_CharSet | T_List | T_String)
        # XXX For String, change spec to "is [not] the empty String" ?
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {NAMED_OPERATION_INVOCATION} is not empty")
    def _(cond, env0, asserting):
        [noi] = cond.children
        env0.assert_expr_is_of_type(noi, T_List)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {var} is now an empty List")
    def _(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_List)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {var} has no elements")
    def _(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_List)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {var} has any elements")
    def _(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_List)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : The length of {var} is {var}")
    def _(cond, env0, asserting):
        [list_var, len_var] = cond.children
        env0.assert_expr_is_of_type(list_var, T_List)
        env0.assert_expr_is_of_type(len_var, T_MathNonNegativeInteger_)
        return (env0, env0)

    @exprd.put(r"{EXPR} : the number of elements in the List {var}")
    @exprd.put(r"{EX} : The number of elements in {var}")
    @exprd.put(r"{EX} : the number of elements in {SETTABLE}")
    @exprd.put(r"{EX} : the number of elements of {var}")
    def _(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_List)
        return (T_MathNonNegativeInteger_, env1)

    @condd.put(r"{CONDITION_1} : {var} has {EX} elements")
    def _(cond, env0, asserting):
        [var, ex] = cond.children
        env0.assert_expr_is_of_type(var, T_List)
        env0.assert_expr_is_of_type(ex, T_MathNonNegativeInteger_)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : the number of elements in the result of {NAMED_OPERATION_INVOCATION} is greater than 2<sup>32</sup> - 1")
    def _(cond, env0, asserting):
        [noi] = cond.children
        env0.assert_expr_is_of_type(noi, T_List)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {var} contains any duplicate entries")
    @condd.put(r"{CONDITION_1} : {var} contains no duplicate entries")
    @condd.put(r"{CONDITION_1} : {var} has any duplicate entries")
    @condd.put(r"{CONDITION_1} : {var} has no duplicate entries")
    @condd.put(r"{CONDITION_1} : {NAMED_OPERATION_INVOCATION} contains any duplicate entries")
    @condd.put(r"{CONDITION_1} : {NAMED_OPERATION_INVOCATION} contains any duplicate elements")
    def _(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_List)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {var} contains a single {nonterminal}")
    def _(cond, env0, asserting):
        [var, nonterminal] = cond.children    
        env0.assert_expr_is_of_type(var, ListType(T_Parse_Node))
        return (env0, env0)

    @condd.put(r'{CONDITION_1} : {EX} is an element of {var}')
    @condd.put(r"{CONDITION_1} : {EX} is not an element of {var}")
    def _(cond, env0, asserting):
        [value_ex, list_var] = cond.children
        env1 = env0.ensure_A_can_be_element_of_list_B(value_ex, list_var)
        return (env1, env1)

    @condd.put(r"{CONDITION_1} : {var} is not currently an element of {var}")
    def _(cond, env0, asserting):
        [item_var, list_var] = cond.children
        env1 = env0.ensure_A_can_be_element_of_list_B(item_var, list_var)
        return (env1, env1)

    @condd.put(r"{CONDITION_1} : {SETTABLE} contains {EX}")
    @condd.put(r"{CONDITION_1} : {EX} does not contain {EX}")
    def _(cond, env0, asserting):
        [container_ex, value_var] = cond.children
        (container_type, container_env) = tc_expr(container_ex, env0)
        if container_type.is_a_subtype_of_or_equal_to(T_String):
            env1 = container_env.ensure_expr_is_of_type(value_var, T_String | T_code_unit_)
        else:
            env1 = env0.ensure_A_can_be_element_of_list_B(value_var, container_ex)
        return (env1, env1)

    @condd.put(r"{CONDITION_1} : {NAMED_OPERATION_INVOCATION} contains {starred_str}")
    def _(cond, env0, asserting):
        [noi, ss] = cond.children
        env0.assert_expr_is_of_type(noi, ListType(T_String))
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {NAMED_OPERATION_INVOCATION} contains more than one occurrence of {starred_str}")
    def _(cond, env0, asserting):
        [noi, ss] = cond.children
        env1 = env0.ensure_expr_is_of_type(noi, ListType(T_String))
        return (env1, env1)

    @condd.put(r"{CONDITION_1} : {NAMED_OPERATION_INVOCATION} contains any duplicate entries for {starred_str} and at least two of those entries were obtained from productions of the form {h_emu_grammar}")
    def _(cond, env0, asserting):
        [noi, ss, emu_grammar] = cond.children
        env1 = env0.ensure_expr_is_of_type(noi, ListType(T_String))
        return (env1, env1)

    @condd.put(r"{CONDITION_1} : {var} does not include the element {LITERAL}")
    def _(cond, env0, asserting):
        [list_var, item_lit] = cond.children
        env1 = env0.ensure_expr_is_of_type(list_var, ListType(T_String))
        env0.assert_expr_is_of_type(item_lit, T_String)
        return (env1, env1)

    @condd.put(r"{CONDITION_1} : {NAMED_OPERATION_INVOCATION} contains any {nonterminal}s")
    def _(cond, env0, asserting):
        [noi, nont] = cond.children
        env0.assert_expr_is_of_type(noi, ListType(T_Parse_Node))
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : there does not exist an element {var} of {var} such that {CONDITION_1}")
    def _(cond, env0, asserting):
        [member_var, list_var, stcond] = cond.children
        env1 = env0.ensure_expr_is_of_type(list_var, ListType(T_String)) # over-specific
        env2 = env1.plus_new_entry(member_var, T_String)
        (t_env, f_env) = tc_cond(stcond, env2)
        return (env1, env1)

    @exprd.put(r"{EXPR} : the first element of {var}")
    @exprd.put(r"{EXPR} : the second element of {var}")
    @exprd.put(r"{EXPR} : the last element in {var}")
    @exprd.put(r"{EXPR} : the last element of {var}")
    def _(expr, env0, _):
        # todo: replace with ad hoc record
        [var] = expr.children
        list_type = env0.assert_expr_is_of_type(var, T_List)
        return (list_type.element_type, env0)

    @exprd.put(r"{EXPR} : the sole element of {PP_NAMED_OPERATION_INVOCATION}")
    @exprd.put(r"{EXPR} : the sole element of {var}")
    def _(expr, env0, _):
        [noi] = expr.children
        list_type = env0.assert_expr_is_of_type(noi, T_List)
        return (list_type.element_type, env0)

    @exprd.put(r"{SETTABLE} : {var}[{EX}]")
    @exprd.put(r"{SETTABLE} : {DOTTING}[{EX}]")
    def _(expr, env0, _):
        [seq_ex, subscript_var] = expr.children
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

# ------------------------------------------------------------------------------
# questions involving multiple Lists:

    @condd.put(r"{CONDITION_1} : {var} and {var} have the same number of elements")
    def _(cond, env0, asserting):
        [vara, varb] = cond.children
        env0.assert_expr_is_of_type(vara, T_List)
        env0.assert_expr_is_of_type(varb, T_List)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {var} and {var} do not have the same number of elements")
    def _(cond, env0, asserting):
        [vara, varb] = cond.children
        env0.assert_expr_is_of_type(vara, T_List)
        env0.assert_expr_is_of_type(varb, T_List)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {var}, {var}, and {var} have the same number of elements")
    def _(cond, env0, asserting):
        [vara, varb, varc] = cond.children
        env0.assert_expr_is_of_type(vara, T_List)
        env0.assert_expr_is_of_type(varb, T_List)
        env0.assert_expr_is_of_type(varc, T_List)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : any element of {NAMED_OPERATION_INVOCATION} also occurs in {NAMED_OPERATION_INVOCATION}")
    def _(cond, env0, asserting):
        [noi1, noi2] = cond.children
        env0.assert_expr_is_of_type(noi1, T_List)
        env0.assert_expr_is_of_type(noi2, T_List)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : any element of {NAMED_OPERATION_INVOCATION} does not also occur in either {NAMED_OPERATION_INVOCATION}, or {NAMED_OPERATION_INVOCATION}")
    def _(cond, env0, asserting):
        [noia, noib, noic] = cond.children
        env0.assert_expr_is_of_type(noia, T_List)
        env0.assert_expr_is_of_type(noib, T_List)
        env0.assert_expr_is_of_type(noic, T_List)
        return (env0, env0)

# ------------------------------------------------------------------------------
# Record:

#> The <dfn>Record</dfn> type
#> is used to describe data aggregations
#> within the algorithms of this specification. 

if 1:
    @exprd.put(r"{EXPR} : a new Record")
    def _(expr, env0, _):
        # Once, in CreateIntrinsics
        [] = expr.children
        return (T_Intrinsics_Record, env0)

#> A Record type value consists of one or more named fields.
#> The value of each field is an ECMAScript language value or specification value.
#> Field names are always enclosed in double brackets, for example [[Value]].

if 1:
    @condd.put(r"{CONDITION_1} : {SETTABLE} has an? {DSBN} field")
    def _(cond, env0, asserting):
        [settable, dsbn] = cond.children
        dsbn_name = dsbn.source_text()[2:-2]
        t = env0.assert_expr_is_of_type(settable, T_Record)
        if t.name == 'Environment Record' and dsbn_name == 'NewTarget':
            add_pass_error(
                cond,
                "STA can't confirm that `%s` could have a `%s` field"
                % ( settable.source_text(), dsbn_name )
            )
            # We could confirm if we looked at the subtypes and what fields they have.
            return env0.with_type_test(settable, 'is a', [T_0, T_Function_Environment_Record], asserting)
        else:
            assert dsbn_name in fields_for_record_type_named_[t.name], (t.name, dsbn_name)
            return (env0, env0)

    @condd.put(r'{CONDITION_1} : {var} does not have an? {DSBN} field')
    def _(cond, env0, asserting):
        [var, dsbn] = cond.children
        env1 = env0.ensure_expr_is_of_type(var, T_Record)
        # XXX We should check whether its type says it *could* have such a field.
        # XXX The particular DSBN could have a (sub-)type-constraining effect
        return (env1, env1)

    @condd.put(r"{CONDITION_1} : That Record's {dsb_word} is {EX}")
    def _(cond, env0, asserting):
        [dsb_word, ex] = cond.children
        dsbn_name = dsb_word.source_text()[2:-2]
        # "That Record" is from prev step's "contains a Record"
        that_type = T_LoadedModule_Record_
        fields = fields_for_record_type_named_[that_type.name]
        field_type = fields[dsbn_name]
        env0.assert_expr_is_of_type(ex, field_type)
        return (env0, env0)

    @tbd.put('{VAL_DESC} : a Record with fields {dsb_word} ({VALUE_DESCRIPTION}) and {dsb_word} ({VALUE_DESCRIPTION})')
    @tbd.put('{VAL_DESC} : a Record with fields {dsb_word} ({VALUE_DESCRIPTION}), {dsb_word} ({VALUE_DESCRIPTION}), and {dsb_word} ({VALUE_DESCRIPTION})')
    @tbd.put('{LIST_ELEMENTS_DESCRIPTION} : Records with fields {dsb_word} ({VAL_DESC}) and {dsb_word} ({VAL_DESC})')
    @tbd.put('{LIST_ELEMENTS_DESCRIPTION} : Records that have {dsb_word} and {dsb_word} fields')
    def _(val_desc, env):
        vd_st = val_desc.source_text()
        t = {
            'a Record with fields [[CharSet]] (a CharSet) and [[Invert]] (a Boolean)': T_CharacterClassResultRecord_,
            'a Record with fields [[CodePoint]] (a code point), [[CodeUnitCount]] (a positive integer), and [[IsUnpairedSurrogate]] (a Boolean)': T_CodePointAt_record_,
            'a Record with fields [[Job]] (a Job Abstract Closure) and [[Realm]] (a Realm Record or *null*)': T_Job_record_,
            'a Record with fields [[Job]] (a Job Abstract Closure) and [[Realm]] (a Realm Record)': T_Job_record_,
            'a Record with fields [[Key]] (a property key) and [[Closure]] (a function object)': T_methodDef_record_,
            'a Record with fields [[Min]] (a non-negative integer) and [[Max]] (a non-negative integer or +&infin;)': T_QuantifierPrefixResultRecord_,
            'a Record with fields [[Min]] (a non-negative integer), [[Max]] (a non-negative integer or +&infin;), and [[Greedy]] (a Boolean)': T_QuantifierResultRecord_,
            'a Record with fields [[Resolve]] (a function object) and [[Reject]] (a function object)': T_ResolvingFunctions_record_,
            'Records with fields [[Key]] (a property key) and [[Value]] (an ECMAScript language value)': T_ImportMeta_record_,
            'Records that have [[Module]] and [[ExportName]] fields': T_ExportResolveSet_Record_,
            'Records with fields [[Specifier]] (a String) and [[Module]] (a Module Record)' : T_LoadedModule_Record_,
        }[vd_st]
        return t

    @tbd.put('{LIST_ELEMENTS_DESCRIPTION} : Record { {dsb_word}: Parse Node, {dsb_word}: Object }')
    def _(led, env):
        led_st = led.source_text()
        t = {
            'Record { [[Site]]: Parse Node, [[Array]]: Object }': T_templateMap_entry_,
        }[led_st]
        return t

    @exprd.put(r"{SETTABLE} : the {DSBN} field of {EXPR}")
    def _(expr, env0, _):
        [dsbn, ex] = expr.children
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

#> For notational convenience within this specification,
#> an object literal-like syntax can be used to express a Record value.

if 1:
    @exprd.put('{RECORD_CONSTRUCTOR} : {RECORD_CONSTRUCTOR_PREFIX} { {FIELDS} }')
    def _(expr, env0, _):
        [record_constructor_prefix, fields] = expr.children
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
                # T_tilde_empty_ | T_continue_ | T_break_,
                # and the static type of _value_ is T_Tangible_ | T_tilde_empty_

                return (T_Tangible_ | T_tilde_empty_ | T_continue_ | T_break_, env0)

            else:
                env1 = env0.ensure_expr_is_of_type(value_ex, T_Tangible_ | T_tilde_empty_)
                (value_type, _) = tc_expr(value_ex, env1) # bleah

                env0.assert_expr_is_of_type(target_ex, T_String | T_tilde_empty_)

                ct = type_corresponding_to_comptype_literal(type_ex)
                if ct == T_Normal:
                    t = value_type
                elif ct == T_throw_:
                    t = ThrowType(value_type)
                else:
                    t = ct

                return (t, env1)

        if constructor_prefix == 'Record':
            field_names = sorted(get_field_names(fields))
            record_type_names = find_record_types_with_fields(field_names)

            if len(record_type_names) == 0:
                add_pass_error(
                    expr,
                    "Could not infer a record type for fields: " + str(field_names)
                )
                record_type_name = 'Record'
                field_info = None

            else:
                if len(record_type_names) == 1:
                    [record_type_name] = record_type_names
                else:
                    if field_names == ['Key', 'Value']:
                        assert record_type_names == ['ImportMeta_record_', 'MapData_record_']
                        # In {Map,WeakMap}.prototype.set
                        record_type_name = 'MapData_record_'

                    elif field_names == ['Value']:
                        assert record_type_names == ['boolean_value_record_', 'integer_value_record_']
                        fst = fields.source_text()
                        if fst == '[[Value]]: *false*':
                            record_type_name = 'boolean_value_record_'
                        elif fst == '[[Value]]: 1':
                            record_type_name = 'integer_value_record_'
                        else:
                            assert 0, fst

                    else:
                        assert 0, field_names

                add_pass_error(
                    expr,
                    "Inferred record type `%s`: be explicit!" % record_type_name
                )
                field_info = fields_for_record_type_named_[record_type_name]

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

    @exprd.put(r"{EXPR} : the Record { {DSBN}, {DSBN} } that is the value of {EX}")
    def _(expr, env0, _):
        [dsbna, dsbnb, ex] = expr.children
        assert dsbna.source_text() == '[[Key]]'
        assert dsbnb.source_text() == '[[Value]]'
        env0.assert_expr_is_of_type(ex, T_MapData_record_)
        return (T_MapData_record_, env0)

#> In specification text and algorithms,
#> dot notation may be used to refer to a specific field of a Record value.
#> For example, if R is the record shown in the previous paragraph then
#> R.[[Field2]] is shorthand for “the field of R named [[Field2]]”.

if 1:
    @exprd.put(r'{DOTTING} : {var}.{DSBN}')
    @exprd.put(r"{DOTTING} : {DOTTING}.{DSBN}")
    def _(expr, env0, _):
        [lhs_var, dsbn] = expr.children
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
                        result_memtype = T_Tangible_ | T_tilde_empty_
                    elif memtype == T_Normal:
                        result_memtype = T_Tangible_ | T_tilde_empty_
                    elif memtype.is_a_subtype_of_or_equal_to(T_Tangible_ | T_tilde_empty_):
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
                    elif memtype in [T_tilde_unused_, ListType(T_code_unit_), T_Top_]:
                        # hm.
                        result_memtype = memtype
                    elif memtype == T_Module_Record:
                        # ContinueDynamicImport
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
                        result_memtype = T_String | T_tilde_empty_
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

        elif lhs_t == T_Object | T_Null:
            # GetValue. (Fix by replacing T_Reference_Record with ReferenceType(base_type)?)
            lhs_t = T_Object
            env2 = env1.with_expr_type_replaced(lhs_var, lhs_t)

        elif lhs_t == T_boolean_value_record_ | T_Boolean:
            lhs_t = T_boolean_value_record_
            env2 = env1.with_expr_type_replaced(lhs_var, lhs_t)

        elif lhs_t == T_Realm_Record | T_Undefined:
            lhs_t = T_Realm_Record
            env2 = env1.with_expr_type_replaced(lhs_var, lhs_t)

        elif lhs_t == T_Cyclic_Module_Record | T_tilde_empty_:
            assert lhs_text in ['_m_.[[CycleRoot]]', '_module_', '_requiredModule_']
            lhs_t = T_Cyclic_Module_Record
            env2 = env1.with_expr_type_replaced(lhs_var, lhs_t)

        elif lhs_t == T_Tangible_:
            # 3 times

            assert dsbn_name == 'AsyncGeneratorState'

            # After:
            #   Let _result_ be Completion(AsyncGeneratorValidate(_generator_, ~empty~)).
            #   IfAbruptRejectPromise(_result_, _promiseCapability_).
            # it's guaranteed that _generator_ is a AsyncGenerator object,
            # but STA isn't smart enough to know that.
            lhs_t = T_AsyncGenerator_object_

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
                    field_type = T_TBD
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
            # lhs_t is presumably a union of types, only one/some of which supports dot-operator
            # In practice, this is a Record type.
            # (In fact, in practice, it's a T_Reference_Record, but I don't need to be that specific.)

            (record_part_of_type, nonrecord_part_of_type) = lhs_t.split_by(T_Record)
            assert record_part_of_type != T_0
            assert nonrecord_part_of_type != T_0

            add_pass_error(
                lhs_var,
                f"Narrowing type {lhs_t} to {record_part_of_type} to support a dot-operator"
            )

            # Okay, but then what's the type of the dotting?
            # Properly, this should be re-submitted.
            assert isinstance(record_part_of_type, NamedType)
            t = fields_for_record_type_named_[record_part_of_type.name][dsbn_name]
            return (t, env2)

# ------------------------------------------------------------------------------
# List of Records

if 1:
    @condd.put(r"{CONDITION_1} : All elements of {var} have their {dsb_word} field set to {LITERAL}, {dsb_word} field set to {LITERAL}, and {dsb_word} field set to {LITERAL}")
    def _(cond, env0, asserting):
        [var, dsb1, lit1, dsb2, lit2, dsb3, lit3] = cond.children
        assert dsb1.source_text() == '[[AsyncEvaluation]]'
        assert dsb2.source_text() == '[[PendingAsyncDependencies]]'
        assert dsb3.source_text() == '[[EvaluationError]]'
        # could check that the lits have the right type.
        env0.assert_expr_is_of_type(var, ListType(T_Cyclic_Module_Record))
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {DOTTING} contains a Record {var} such that {CONDITION_1}")
    def _(cond, env0, asserting):
        [ex, var, stcond] = cond.children
        (ex_t, env1) = tc_expr(ex, env0); assert env1 is env0
        assert ex_t.is_a_subtype_of_or_equal_to(T_List)
        assert ex_t.element_type.is_a_subtype_of_or_equal_to(T_Record)
        env_for_cond = env0.plus_new_entry(var, ex_t.element_type)
        (cond_t_env, cond_f_env) = tc_cond(stcond, env_for_cond)
        return (cond_t_env, env0)

    @condd.put(r"{CONDITION_1} : {EX} contains a Record whose {dsb_word} is {var}")
    @condd.put(r"{CONDITION_1} : Exactly one element of {DOTTING} is a Record whose {dsb_word} is {var}")
    def _(cond, env0, asserting):
        [list_ex, dsb_word, var] = cond.children
        dsbn_name = dsb_word.source_text()[2:-2]
        (list_type, env1) = tc_expr(list_ex, env0); assert env1 is env0
        assert isinstance(list_type, ListType)
        et = list_type.element_type
        fields = fields_for_record_type_named_[et.name]
        field_type = fields[dsbn_name]
        env1.assert_expr_is_of_type(var, field_type)
        return (env0, env0)

    @exprd.put(r"{EXPR} : the element in {EX} whose {DSBN} is {EX}")
    @exprd.put(r"{EXPR} : the element of {EX} whose {DSBN} field is {var}")
    @exprd.put(r"{EXPR} : the element of {EX} whose {DSBN} is the same as {EX}")
    def _(expr, env0, _):
        [list_ex, dsbn, val_ex] = expr.children
        dsbn_name = dsbn.source_text()[2:-2]
        (list_type, env1) = tc_expr(list_ex, env0); assert env1 is env0
        assert isinstance(list_type, ListType)
        et = list_type.element_type
        assert isinstance(et, NamedType)
        fields = fields_for_record_type_named_[et.name]
        whose_type = fields[dsbn_name]
        env1.assert_expr_is_of_type(val_ex, whose_type)
        return (et, env1)

    @exprd.put(r"{EXPR} : the Record in {DOTTING} whose {dsb_word} is {var}")
    def _(expr, env0, _):
        [dotting, dsb_word, var] = expr.children
        dsbn_name = dsb_word.source_text()[2:-2]
        (list_type, env1) = tc_expr(dotting, env0); assert env1 is env0
        assert isinstance(list_type, ListType)
        et = list_type.element_type
        fields = fields_for_record_type_named_[et.name]
        whose_type = fields[dsbn_name]
        env1.assert_expr_is_of_type(var, whose_type)
        return (et, env0)

# ==============================================================================
#@ 6.2.3 The Set and Relation Specification Types

#> Values of the Relation type
#> are Sets of ordered pairs of values from its value domain.

if 1:
    @exprd.put(r"{EXPR} : an empty Set")
    def _(expr, env0, _):
        [] = expr.children
        return (T_Set, env0)

    @exprd.put(r"{PAIR} : ({EX}, {EX})")
    def _(expr, env0, _):
        [a, b] = expr.children
        # over-specific:
        env0.assert_expr_is_of_type(a, T_event_)
        env0.assert_expr_is_of_type(b, T_event_)
        return (T_event_pair_, env0)

    @nv.put(r'{COMMAND} : Add {var} to {var}.')
    @nv.put(r"{SMALL_COMMAND} : add {var} to {var}")
    def _(anode, env0):
        [item_var, collection_var] = anode.children
        (item_type, env1) = tc_expr(item_var, env0); assert env1 is env0
        (collection_type, env2) = tc_expr(collection_var, env0); assert env2 is env0
        if item_type.is_a_subtype_of_or_equal_to(T_event_) and collection_type == T_Set:
            pass
        else:
            assert 0
        return env0

    @condd.put(r"{CONDITION_1} : the pairs {PAIR} and {PAIR} are in {EX}")
    @condd.put(r"{CONDITION_1} : the pairs {PAIR} and {PAIR} are not in {EX}")
    @condd.put(r"{CONDITION_1} : either {PAIR} or {PAIR} is in {EX}")
    def _(cond, env0, asserting):
        [paira, pairb, ex] = cond.children
        env0.assert_expr_is_of_type(paira, T_event_pair_)
        env0.assert_expr_is_of_type(pairb, T_event_pair_)
        env0.assert_expr_is_of_type(ex, T_Relation)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {var} is not in {PREFIX_PAREN}")
    def _(cond, env0, asserting):
        [item_var, set_pp] = cond.children
        env0.assert_expr_is_of_type(set_pp, T_Set)
        env0.assert_expr_is_of_type(item_var, T_event_)
        return (env0, env0)

# ==============================================================================
#@ 6.2.4 The Completion Record Specification Type

#> The following shorthand terms are sometimes used to refer to Completion Records.

if 1:
    tbd['{VAL_DESC} : a Completion Record'] = T_Abrupt | T_Normal
    tbd['{VAL_DESC} : a normal completion'] = T_Normal
    tbd['{VAL_DESC} : a return completion'] = T_return_
    tbd['{VAL_DESC} : a throw completion'] = T_throw_
    tbd['{VAL_DESC} : an abrupt completion'] = T_Abrupt
    tbd['{VAL_DESC} : any value except a Completion Record'] = T_Tangible_ | T_Intangible_

    @tbd.put('{VAL_DESC} : a normal completion containing {VALUE_DESCRIPTION}')
    def _(vd, env):
        [child] = vd.children
        return type_bracket_for(child, env)

    @condd.put(r"{CONDITION_1} : {var} is a normal completion with a value of {LITERAL}. The possible sources of this value are Await or, if the async function doesn't await anything, step {h_emu_xref} above")
    def _(cond, env0, asserting):
        [var, literal, _] = cond.children
        env0.assert_expr_is_of_type(literal, T_tilde_unused_)
        return env0.with_type_test(var, 'is a', T_tilde_unused_, asserting)

    @exprd.put(r"{EXPR} : a new implementation-defined Completion Record")
    def _(expr, env0, _):
        [] = expr.children
        return (T_Abrupt | T_Normal, env0)

# ---------

    @condd.put(r"{CONDITION_1} : The next step never returns an abrupt completion because {CONDITION_1}")
    def _(cond, env0, asserting):
        [subcond] = cond.children
        return tc_cond(subcond, env0, asserting)

# ==============================================================================
#@ 6.2.5 The Reference Record Specification Type

if 1:
    tbd['{VAL_DESC} : a Reference Record'] = T_Reference_Record
    tbd['{VAL_DESC} : a Super Reference Record'] = a_subset_of(T_Reference_Record)

# ==============================================================================
#@ 6.2.6 The Property Descriptor Specification Type

if 1:
    tbd['{VAL_DESC} : a Property Descriptor'] = T_Property_Descriptor
    tbd['{VAL_DESC} : a fully populated Property Descriptor'] = a_subset_of(T_Property_Descriptor)

    @exprd.put(r"{EXPR} : a newly created Property Descriptor with no fields")
    @exprd.put(r"{EXPR} : a new Property Descriptor that initially has no fields")
    def _(expr, env0, _):
        [] = expr.children
        return (T_Property_Descriptor, env0)

    @exprd.put(r"{EXPR} : the fully populated data Property Descriptor for the property, containing the specified attributes for the property. For properties listed in {h_emu_xref}, {h_emu_xref}, or {h_emu_xref} the value of the {DSBN} attribute is the corresponding intrinsic object from {var}")
    def _(expr, env0, _):
        [emu_xref1, emu_xref2, emu_xref3, dsbn, var] = expr.children
        env0.assert_expr_is_of_type(var, T_Realm_Record)
        return (T_Property_Descriptor, env0)

    @condd.put(r"{CONDITION_1} : {var} does not have any fields")
    def _(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_Property_Descriptor)
        return (env0, env0)

    @condd.put(r'{CONDITION_1} : {var} has attribute values { {DSBN}: *true*, {DSBN}: *true* }')
    def _(cond, env0, asserting):
        [var, dsbn1, dsbn2] = cond.children
        env1 = env0.ensure_expr_is_of_type(var, T_Property_Descriptor)
        assert dsbn1.source_text() == '[[Writable]]'
        assert dsbn2.source_text() == '[[Enumerable]]'
        return (env1, env1)

    @nv.put(r"{EACH_THING} : field of {var}")
    def _(each_thing, env0):
        [desc_var] = each_thing.children
        loop_var = None # todo: no loop variable!
        env0.assert_expr_is_of_type(desc_var, T_Property_Descriptor)
        return env0

# ==============================================================================
#@ 6.2.7 The Environment Record Specification Type

# (See 9.1 Environment Records)

# ==============================================================================
#@ 6.2.8 The Abstract Closure Specification Type

    tbd['{VAL_DESC} : an Abstract Closure with no parameters'] = ProcType([], T_Top_)
    tbd['{VAL_DESC} : an Abstract Closure with two parameters'] = ProcType([T_Tangible_, T_Tangible_], T_Number | T_throw_)
    tbd['{VAL_DESC} : an Abstract Closure'] = T_proc_

    @exprd.put(r"{MULTILINE_EXPR} : a new {CLOSURE_KIND} with {CLOSURE_PARAMETERS} that captures {CLOSURE_CAPTURES} and performs the following {CLOSURE_STEPS} when called:{IND_COMMANDS}")
    def _(expr, env0, _):
        [clo_kind, clo_parameters, clo_captures, _, commands] = expr.children
        clo_kind = clo_kind.source_text()

        #XXX Should assert no intersection between clo_parameters and clo_captures

        # -----

        env_for_commands = Env()

        n_parameters = len(clo_parameters.children)
        # polymorphic
        if clo_kind == 'Abstract Closure':
            clo_param_types = [T_TBD] * n_parameters
        elif clo_kind == 'MatcherContinuation':
            assert n_parameters == 1
            clo_param_types = [T_MatchState]
        elif clo_kind == 'Matcher':
            assert n_parameters == 2
            clo_param_types = [T_MatchState, T_MatcherContinuation]
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

# ==============================================================================
#@ 6.2.9 Data Blocks

if 1:
    tbd['{VAL_DESC} : a Data Block'] = T_Data_Block
    tbd['{VAL_DESC} : a Shared Data Block'] = T_Shared_Data_Block
    tbd['{VAL_DESC} : a Shared Data Block event'] = T_Shared_Data_Block_event

    @exprd.put(r'{EXPR} : a new Data Block value consisting of {var} bytes. If it is impossible to create such a Data Block, throw a {ERROR_TYPE} exception')
    def _(expr, env0, _):
        [var, error_type] = expr.children
        (t, env1) = tc_expr(var, env0)
        assert env1 is env0
        assert t.is_a_subtype_of_or_equal_to(T_MathInteger_)
        proc_add_return(env0, ThrowType(type_for_ERROR_TYPE(error_type)), error_type)
        return (T_Data_Block, env1)

    @exprd.put(r'{EXPR} : a new Shared Data Block value consisting of {var} bytes. If it is impossible to create such a Shared Data Block, throw a {ERROR_TYPE} exception')
    def _(expr, env0, _):
        [var, error_type] = expr.children
        (t, env1) = tc_expr(var, env0)
        assert env1 is env0
        assert t.is_a_subtype_of_or_equal_to(T_MathInteger_)
        proc_add_return(env0, ThrowType(type_for_ERROR_TYPE(error_type)), error_type)
        return (T_Shared_Data_Block, env1)

    @condd.put(r"{CONDITION_1} : {EX} and {EX} are the same Shared Data Block values")
    def _(cond, env0, asserting):
        [exa, exb] = cond.children
        env1 = env0.ensure_expr_is_of_type(exa, T_Shared_Data_Block)
        env2 = env1.ensure_expr_is_of_type(exb, T_Shared_Data_Block)
        return (env2, env2)

    @nv.put(r'{COMMAND} : Set all of the bytes of {var} to 0.')
    def _(anode, env0):
        [var] = anode.children
        env1 = env0.ensure_expr_is_of_type(var, T_Data_Block)
        return env1

    @nv.put(r"{SMALL_COMMAND} : store the individual bytes of {var} into {var}, starting at {var}[{var}]")
    @nv.put(r"{COMMAND} : Store the individual bytes of {var} into {var}, starting at {var}[{var}].")
    def _(anode, env0):
        [var1, var2, var3, var4] = anode.children
        env0.assert_expr_is_of_type(var1, ListType(T_MathInteger_))
        env1 = env0.ensure_expr_is_of_type(var2, T_Data_Block)
        assert var3.children == var2.children
        env0.assert_expr_is_of_type(var4, T_MathInteger_)
        return env1

    @exprd.put(r"{EXPR} : the number of bytes in {var}")
    def _(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_Data_Block | T_Shared_Data_Block)
        return (T_MathNonNegativeInteger_, env1)

    @exprd.put(r"{EXPR} : a List of length {var} whose elements are the sequence of {var} bytes starting with {var}[{var}]")
    def _(expr, env0, _):
        [var1, var2, var3, var4] = expr.children
        assert var1.children == var2.children
        env0.assert_expr_is_of_type(var1, T_MathInteger_)
        env1 = env0.ensure_expr_is_of_type(var3, T_Data_Block | T_Shared_Data_Block)
        env0.assert_expr_is_of_type(var4, T_MathInteger_)
        return (ListType(T_MathInteger_), env1)

    @exprd.put(r"{EXPR} : a List whose elements are bytes from {var} at indices in {INTERVAL}")
    def _(expr, env0, _):
        [data_var, interval] = expr.children
        env1 = env0.ensure_expr_is_of_type(data_var, T_Data_Block | T_Shared_Data_Block)
        env1.assert_expr_is_of_type(interval, T_MathNonNegativeInteger_)
        return (ListType(T_MathNonNegativeInteger_), env1)

    @nv.put(r"{EACH_THING} : index {var} of {var}")
    def _(each_thing, env0):
        [loop_var, collection_var] = each_thing.children
        env0.assert_expr_is_of_type(collection_var, T_Shared_Data_Block)
        return env0.plus_new_entry(loop_var, T_MathInteger_)

    @condd.put(r"{CONDITION_1} : {EX} and {EX} are valid byte offsets within the memory of {var}")
    def _(cond, env0, asserting):
        [offset1, offset2, sdb] = cond.children
        env1 = env0.ensure_expr_is_of_type(offset1, T_MathInteger_)
        env1.assert_expr_is_of_type(offset2, T_MathInteger_)
        env1.assert_expr_is_of_type(sdb, T_Shared_Data_Block)
        return (env1, env1)

# ==============================================================================
#@ 6.2.10 The PrivateElement Specification Type

if 1:
    tbd['{VAL_DESC} : a PrivateElement'] = T_PrivateElement
    tbd['{LIST_ELEMENTS_DESCRIPTION} : PrivateElements'                    ] = T_PrivateElement

    @condd.put(r"{CONDITION_1} : {EX} contains a PrivateElement whose {dsb_word} is {var}")
    def _(cond, env0, asserting):
        [ex, dsb_word, var] = cond.children
        env0.assert_expr_is_of_type(ex, ListType(T_PrivateElement))
        assert dsb_word.source_text() == '[[Key]]'
        env0.assert_expr_is_of_type(var, T_Private_Name)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {var} contains a PrivateElement whose {dsb_word} is {DOTTING}")
    def _(cond, env0, asserting):
        [var, dsb_word, dotting] = cond.children
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_PrivateElement))
        assert dsb_word.source_text() == '[[Key]]'
        env1.assert_expr_is_of_type(dotting, T_Private_Name)
        return (env1, env1)

    @exprd.put(r"{EXPR} : that PrivateElement")
    def _(expr, env0, _):
        [] = expr.children
        return (T_PrivateElement, env0)

# ==============================================================================
#@ 6.2.11 The ClassFieldDefinition Record Specification Type

if 1:
    tbd['{VAL_DESC} : a ClassFieldDefinition Record'] = T_ClassFieldDefinition_Record
    tbd['{LIST_ELEMENTS_DESCRIPTION} : ClassFieldDefinition Records'] = T_ClassFieldDefinition_Record

# ==============================================================================
#@ 6.2.12 Private Names

if 1:
    tbd['{VAL_DESC} : a Private Name'] = T_Private_Name
    tbd['{LIST_ELEMENTS_DESCRIPTION} : Private Names'] = T_Private_Name
    tbd['{VAL_DESC} : a property key or Private Name'] = T_String | T_Symbol | T_Private_Name

    @condd.put(r"{CONDITION_1} : {EX} contains a Private Name whose {dsb_word} is {var}")
    def _(cond, env0, asserting):
        [ex, dsb_word, var] = cond.children
        env0.assert_expr_is_of_type(ex, ListType(T_Private_Name))
        assert dsb_word.source_text() == '[[Description]]'
        env0.assert_expr_is_of_type(var, T_String)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : Exactly one element of {var} is a Private Name whose {dsb_word} is {var}")
    def _(cond, env0, asserting):
        [list_var, dsb_word, var] = cond.children
        env0.assert_expr_is_of_type(list_var, ListType(T_Private_Name))
        assert dsb_word.source_text() == '[[Description]]'
        env0.assert_expr_is_of_type(var, T_String)
        return (env0, env0)

    @exprd.put(r"{EXPR} : a new Private Name whose {dsb_word} value is {var}")
    def _(expr, env0, _):
        [dsb_word, var] = expr.children
        assert dsb_word.source_text() == '[[Description]]'
        env0.assert_expr_is_of_type(var, T_String)
        return (T_Private_Name, env0)

    @exprd.put(r"{EXPR} : the Private Name in {var} whose {dsb_word} is {var}")
    def _(expr, env0, _):
        [list_var, dsb_word, var] = expr.children
        env0.assert_expr_is_of_type(list_var, ListType(T_Private_Name))
        assert dsb_word.source_text() == '[[Description]]'
        env0.assert_expr_is_of_type(var, T_String)
        return (T_Private_Name, env0)

    @exprd.put(r"{EXPR} : that Private Name")
    def _(expr, env0, _):
        [] = expr.children
        return (T_Private_Name, env0)

# ==============================================================================
#@ 6.2.13 The ClassStaticBlockDefinition Record Specification Type

if 1:
    tbd['{VAL_DESC} : a ClassStaticBlockDefinition Record'] = T_ClassStaticBlockDefinition_Record

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 7 Abstract Operations

# ==============================================================================
#@ 7.1.13 ToBigInt

if 1:
    @exprd.put(r"{EXPR} : the value that {var} corresponds to in {h_emu_xref}")
    def _(expr, env0, _):
        [var, xref] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_Primitive)
        assert xref.source_text() == '<emu-xref href="#table-tobigint"></emu-xref>'
        return (T_BigInt | ThrowType(T_TypeError) | ThrowType(T_SyntaxError), env1)

# ==============================================================================
#@ 7.4.1 Iterator Records

if 1:
    tbd['{VAL_DESC} : an Iterator Record'] = T_Iterator_Record

# ==============================================================================
#@ 7.4.8 IfAbruptCloseIterator

if 1:
    @nv.put(r"{COMMAND} : IfAbruptCloseIterator({var}, {var}).")
    def _(anode, env0):
        [vara, varb] = anode.children
        env0.assert_expr_is_of_type(vara, T_Normal | T_Abrupt)
        env0.assert_expr_is_of_type(varb, T_Iterator_Record)

        proc_add_return(env0, T_Tangible_ | T_tilde_empty_ | T_throw_, anode)

        (ta, tenv) = tc_expr(vara, env0); assert tenv is env0
        (normal_part_of_ta, abnormal_part_of_ta) = ta.split_by(T_Normal)
        return env0.with_expr_type_narrowed(vara, normal_part_of_ta)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 8 Syntax-Directed Operations

# ==============================================================================
#@ 8.5.1 Static Semantics: Contains

if 1:
    @condd.put(r"{CONDITION_1} : {LOCAL_REF} Contains {G_SYM}") # spec bug: should say "is *true*"
    def _(cond, env0, asserting):
        [local_ref, g_sym] = cond.children
        env0.assert_expr_is_of_type(local_ref, T_Parse_Node)
        return (env0, env0)

    @exprd.put(r"{NAMED_OPERATION_INVOCATION} : {LOCAL_REF} Contains {var}")
    @exprd.put(r"{NAMED_OPERATION_INVOCATION} : {LOCAL_REF} Contains {G_SYM}")
    def _(expr, env0, _):
        [lhs, rhs] = expr.children
        return tc_sdo_invocation('Contains', lhs, [rhs], expr, env0)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 9 Executable Code and Execution Contexts

# ==============================================================================
#@ 9.1 Environment Records

def type_for_environment_record_kind(kind):
    return NamedType(kind.source_text() + ' Environment Record')

if 1:
    tbd['{VAL_DESC} : an Environment Record'] = T_Environment_Record

    @tbd.put('{VAL_DESC} : an? {ENVIRONMENT_RECORD_KIND} Environment Record')
    def _(val_desc, env):
        [kind] = val_desc.children
        return type_for_environment_record_kind(kind)

    @exprd.put(r'{EXPR} : a new {ENVIRONMENT_RECORD_KIND} Environment Record containing no bindings')
    @exprd.put(r'{EXPR} : a new {ENVIRONMENT_RECORD_KIND} Environment Record')
    def _(expr, env0, _):
        [kind] = expr.children
        t = type_for_environment_record_kind(kind)
        return (t, env0)

# ==============================================================================
#@ 9.1.1.1 Declarative Environment Records

if 1:
    @nv.put(r"{COMMAND} : Create an immutable binding in {var} for {var} and record that it is uninitialized. If {var} is *true*, record that the newly created binding is a strict binding.")
    @nv.put(r"{COMMAND} : Create a mutable binding in {var} for {var} and record that it is uninitialized. If {var} is *true*, record that the newly created binding may be deleted by a subsequent DeleteBinding call.")
    def _(anode, env0):
        [er_var, n_var, s_var] = anode.children
        env0.assert_expr_is_of_type(er_var, T_Environment_Record)
        env0.assert_expr_is_of_type(n_var, T_String)
        env0.assert_expr_is_of_type(s_var, T_Boolean)
        return env0

    @nv.put(r"{COMMAND} : {h_emu_not_ref_Record} that the binding for {var} in {var} has been initialized.")
    def _(anode, env0):
        [_, key_var, oer_var] = anode.children
        env0.assert_expr_is_of_type(key_var, T_String)
        env0.assert_expr_is_of_type(oer_var, T_Environment_Record)
        return env0

    @nv.put(r"{COMMAND} : Remove the binding for {var} from {var}.")
    def _(anode, env0):
        [n_var, er_var] = anode.children
        env0.assert_expr_is_of_type(n_var, T_String)
        env0.assert_expr_is_of_type(er_var, T_Environment_Record)
        return env0

    @condd.put(r"{CONDITION_1} : {var} does not already have a binding for {var}")
    @condd.put(r"{CONDITION_1} : {var} does not have a binding for {var}")
    @condd.put(r"{CONDITION_1} : {var} has a binding for the name that is the value of {var}")
    @condd.put(r"{CONDITION_1} : {var} has a binding for {var}")
    @condd.put(r"{CONDITION_1} : {var} must have an uninitialized binding for {var}")
    def _(cond, env0, asserting):
        [er_var, n_var] = cond.children
        env0.assert_expr_is_of_type(er_var, T_Environment_Record)
        env0.assert_expr_is_of_type(n_var, T_String)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : the binding for {var} in {var} cannot be deleted")
    @condd.put(r"{CONDITION_1} : the binding for {var} in {var} has not yet been initialized")
    @condd.put(r"{CONDITION_1} : the binding for {var} in {var} is a mutable binding")
    @condd.put(r"{CONDITION_1} : the binding for {var} in {var} is a strict binding")
    @condd.put(r"{CONDITION_1} : the binding for {var} in {var} is an uninitialized binding")
    def _(cond, env0, asserting):
        [n_var, er_var] = cond.children
        env0.assert_expr_is_of_type(n_var, T_String)
        env0.assert_expr_is_of_type(er_var, T_Environment_Record)
        return (env0, env0)

    @exprd.put(r"{EXPR} : the value currently bound to {var} in {var}")
    @exprd.put(r"{SETTABLE} : the bound value for {var} in {var}")
    def _(expr, env0, _):
        [n_var, er_var] = expr.children
        env0.assert_expr_is_of_type(n_var, T_String)
        env0.assert_expr_is_of_type(er_var, T_Environment_Record)
        return (T_Tangible_, env0)

    # 9.1.1.1.5 SetMutableBinding
    @nv.put(r"{SMALL_COMMAND} : change its bound value to {var}")
    def _(anode, env0):
        # elliptical
        [var] = anode.children
        env0.assert_expr_is_of_type(var, T_Tangible_)
        return env0

    # 9.1.1.1.5 SetMutableBinding
    @condd.put(r"{CONDITION_1} : This is an attempt to change the value of an immutable binding")
    def _(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

# ==============================================================================
#@ 9.1.1.4 Global Environment Records

if 1:
    @condd.put(r"{CONDITION_1} : the binding exists")
    def _(cond, env0, asserting):
        # elliptical
        [] = cond.children
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : it must be in the Object Environment Record")
    def _(cond, env0, asserting):
        # elliptical
        [] = cond.children
        return (env0, env0)

# ==============================================================================
#@ 9.1.1.5 Module Environment Records

if 1:
    @nv.put(r'{COMMAND} : Create an immutable indirect binding in {var} for {var} that references {var} and {var} as its target binding and record that the binding is initialized.')
    def _(anode, env0):
        [er_var, n_var, m_var, n2_var] = anode.children
        env0.assert_expr_is_of_type(er_var, T_Environment_Record)
        env0.assert_expr_is_of_type(n_var, T_String)
        env0.assert_expr_is_of_type(m_var, T_Module_Record)
        env0.assert_expr_is_of_type(n2_var, T_String)
        return env0

    @condd.put(r"{CONDITION_1} : the binding for {var} is an indirect binding")
    def _(cond, env0, asserting):
        # todo: make ER explicit in spec?
        [n_var] = cond.children
        env0.assert_expr_is_of_type(n_var, T_String)
        return (env0, env0)

    @condd.put(r'{CONDITION_1} : When {SETTABLE} is instantiated, it will have a direct binding for {var}')
    def _(cond, env0, asserting):
        [settable, var] = cond.children
        env0.assert_expr_is_of_type(settable, T_Environment_Record | T_tilde_empty_)
        env0.assert_expr_is_of_type(var, T_String)
        return (env0, env0)

# ==============================================================================
#@ 9.2 PrivateEnvironment Records

if 1:
    tbd['{VAL_DESC} : a PrivateEnvironment Record'] = T_PrivateEnvironment_Record

# ==============================================================================
#@ 9.3 Realms

if 1:
    tbd['{VAL_DESC} : a Realm Record'] = T_Realm_Record

    @exprd.put(r"{EXPR} : a new Realm Record")
    def _(expr, env0, _):
        [] = expr.children
        return (T_Realm_Record, env0)

    @exprd.put(r'{EX} : the current Realm Record')
    def _(expr, env0, _):
        [] = expr.children
        return (T_Realm_Record, env0)

    @condd.put(r"{CONDITION_1} : {var} and {var} are not the same Realm Record")
    def _(cond, env0, asserting):
        [avar, bvar] = cond.children
        env0.assert_expr_is_of_type(avar, T_Realm_Record)
        env0.assert_expr_is_of_type(bvar, T_Realm_Record)
        return (env0, env0)

    tbd['{VAL_DESC} : a Record whose field names are intrinsic keys and whose values are objects'] = T_Intrinsics_Record

    # 9.3.2 CreateIntrinsics
    @nv.put(r"{COMMAND} : Set fields of {DOTTING} with the values listed in {h_emu_xref}. {the_field_names_are_the_names_listed_etc}")
    def _(anode, env0):
        [var, emu_xref, _] = anode.children
        env0.assert_expr_is_of_type(var, T_Intrinsics_Record)
        return env0

# ==============================================================================
#@ 9.4 Execution Contexts

#> An <dfn>execution context</dfn> is a specification device
#> that is used to track the runtime evaluation of code
#> by an ECMAScript implementation.

if 1:
    tbd['{VAL_DESC} : an execution context'] = T_execution_context
    tbd['{VAL_DESC} : an ECMAScript execution context'] = T_execution_context

    @exprd.put(r"{EXPR} : a new execution context")
    def _(expr, env0, _):
        [] = expr.children
        return (T_execution_context, env0)

# ------------------------------------------------------------------------------
#> At any point in time,
#> there is at most one execution context per agent that is actually executing code.
#> This is known as the agent's <dfn>running execution context</dfn>.
#> All references to the running execution context in this specification
#> denote the running execution context of the surrounding agent.

    @exprd.put(r'{EXPR} : the running execution context')
    def _(expr, env0, _):
        [] = expr.children
        return (T_execution_context, env0)

    @condd.put(r"{CONDITION_1} : {var} is now the running execution context")
    def _(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_execution_context)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : {var} is the running execution context again")
    def _(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_execution_context)
        return (env0, env0)

# ------------------------------------------------------------------------------
#> The <dfn>execution context stack</dfn> is used to track execution contexts.
#> The running execution context is always the top element of this stack.

    @nv.put(r'{COMMAND} : Push {var} onto the execution context stack; {var} is now the running execution context.')
    def _(anode, env0):
        [var1, var2] = anode.children
        assert var1.children == var2.children
        env1 = env0.ensure_expr_is_of_type(var1, T_execution_context)
        return env1

    @nv.put(r'{COMMAND} : Remove {var} from the execution context stack and restore the execution context that is at the top of the execution context stack as the running execution context.')
    def _(anode, env0):
        [var] = anode.children
        env0.assert_expr_is_of_type(var, T_execution_context)
        return env0

    @nv.put(r"{COMMAND} : Remove {var} from the execution context stack and restore {var} as the running execution context.")
    def _(anode, env0):
        [avar, bvar] = anode.children
        env0.assert_expr_is_of_type(avar, T_execution_context)
        env0.assert_expr_is_of_type(bvar, T_execution_context)
        return env0

    @nv.put(r"{COMMAND} : Remove {var} from the execution context stack.")
    def _(anode, env0):
        [avar] = anode.children
        env0.assert_expr_is_of_type(avar, T_execution_context)
        return env0

    # 9.4.1
    @exprd.put(r'{EXPR} : the topmost execution context on the execution context stack whose ScriptOrModule component is not {LITERAL}')
    def _(expr, env0, _):
        [literal] = expr.children
        return (T_execution_context, env0)

    # 9.4.1
    @condd.put(r'{CONDITION_1} : no such execution context exists')
    def _(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

    @exprd.put(r"{EXPR} : the second to top element of the execution context stack")
    def _(expr, env0, _):
        [] = expr.children
        return (T_execution_context, env0)

    @condd.put(r"{CONDITION_1} : The execution context stack has at least two elements")
    @condd.put(r"{CONDITION_1} : The execution context stack is not empty")
    @condd.put(r"{CONDITION_1} : the execution context stack is empty")
    def _(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

# ------------------------------------------------------------------------------
#> Each execution context has at least the state components listed in
#> <emu-xref href="#table-state-components-for-all-execution-contexts"></emu-xref>.

    @exprd.put(r"{SETTABLE} : the {EXECUTION_CONTEXT_COMPONENT} component of {var}")
    @exprd.put(r"{SETTABLE} : The {EXECUTION_CONTEXT_COMPONENT} of {var}")
    @exprd.put(r"{SETTABLE} : the {EXECUTION_CONTEXT_COMPONENT} of {var}")
    @exprd.put(r"{SETTABLE} : {var}'s {EXECUTION_CONTEXT_COMPONENT}")
    def _(expr, env0, _):
        if expr.prod.rhs_s.endswith('{var}'):
            [component_name, var] = expr.children
        else:
            [var, component_name] = expr.children

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

    @exprd.put(r"{SETTABLE} : the running execution context's {EXECUTION_CONTEXT_COMPONENT}")
    @exprd.put(r"{SETTABLE} : the {EXECUTION_CONTEXT_COMPONENT} of the running execution context")
    def _(expr, env0, _):
        [component_name] = expr.children
        t = {
            'LexicalEnvironment' : T_Environment_Record,
            'VariableEnvironment': T_Environment_Record,
            'PrivateEnvironment' : T_PrivateEnvironment_Record, # | T_Null
            'Realm'              : T_Realm_Record,
        }[component_name.source_text()]
        return (t, env0)

# ------------------------------------------------------------------------------
#> Evaluation of code by the running execution context
#> may be suspended at various points defined within this specification.

    @nv.put(r"{COMMAND} : {h_emu_meta_start}Resume the suspended evaluation of {var}{h_emu_meta_end}. Let {var} be the value returned by the resumed computation.")
    def _(anode, env0):
        [_, ctx_var, _, b_var] = anode.children
        env0.assert_expr_is_of_type(ctx_var, T_execution_context)
        return env0.plus_new_entry(b_var, T_Tangible_ | T_return_ | T_throw_)

    @nv.put(r"{COMMAND} : {h_emu_meta_start}Resume the suspended evaluation of {var}{h_emu_meta_end} using {EX} as the result of the operation that suspended it.")
    def _(anode, env0):
        [_, ctx_var, _, resa_ex] = anode.children
        env0.assert_expr_is_of_type(ctx_var, T_execution_context)
        env1 = env0.ensure_expr_is_of_type(resa_ex, T_Tangible_ | T_tilde_empty_ | T_return_ | T_throw_)
        return env1

    @nv.put(r"{COMMAND} : {h_emu_meta_start}Resume the suspended evaluation of {var}{h_emu_meta_end} using {EX} as the result of the operation that suspended it. Let {var} be the Completion Record returned by the resumed computation.")
    @nv.put(r"{COMMAND} : {h_emu_meta_start}Resume the suspended evaluation of {var}{h_emu_meta_end} using {EX} as the result of the operation that suspended it. Let {var} be the value returned by the resumed computation.")
    def _(anode, env0):
        [_, ctx_var, _, resa_ex, resb_var] = anode.children
        env0.assert_expr_is_of_type(ctx_var, T_execution_context)
        env1 = env0.ensure_expr_is_of_type(resa_ex, T_Tangible_ | T_tilde_empty_ | T_return_ | T_throw_)
        return env1.plus_new_entry(resb_var, T_Tangible_)

    @nv.put(r"{COMMAND} : Resume the context that is now on the top of the execution context stack as the running execution context.")
    def _(anode, env0):
        [] = anode.children
        return env0

    @nv.put(r"{COMMAND} : Resume {var} passing {EX}. If {var} is ever resumed again, let {var} be the Completion Record with which it is resumed.")
    def _(anode, env0):
        [vara, exb, varc, vard] = anode.children
        env0.assert_expr_is_of_type(vara, T_execution_context)
        env0.assert_expr_is_of_type(exb, T_Tangible_ | T_tilde_empty_)
        env0.assert_expr_is_of_type(varc, T_execution_context)
        return env0.plus_new_entry(vard, T_Tangible_ | T_tilde_empty_)

    @nv.put(r"{COMMAND} : Suspend {var} and remove it from the execution context stack.")
    def _(anode, env0):
        [var] = anode.children
        env0.assert_expr_is_of_type(var, T_execution_context)
        return env0

    @nv.put(r"{COMMAND} : Suspend the running execution context.")
    def _(anode, env0):
        [] = anode.children
        return env0

    @nv.put(r'{SMALL_COMMAND} : suspend {var}')
    def _(anode, env0):
        [var] = anode.children
        env0.assert_expr_is_of_type(var, T_execution_context)
        return env0

    @nv.put(r'{COMMAND} : Suspend {var}.')
    def _(anode, env0):
        [var] = anode.children
        return env0.ensure_expr_is_of_type(var, T_execution_context)

    @nv.put(r"{COMMAND} : Set {SETTABLE} such that when evaluation is resumed for that execution context the following steps will be performed:{IND_COMMANDS}")
    def _(anode, env0):
        [settable, commands] = anode.children
        env0.assert_expr_is_of_type(settable, T_host_defined_)
        defns = [(None, commands)]
        env_at_bottom = tc_proc(None, defns, env0)
        return env0

    @condd.put(r'{CONDITION_1} : {var} is not already suspended')
    def _(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_execution_context)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : When we return here, {var} has already been removed from the execution context stack and {var} is the currently running execution context")
    def _(cond, env0, asserting):
        [a_var, b_var] = cond.children
        env0.assert_expr_is_of_type(a_var, T_execution_context)
        env0.assert_expr_is_of_type(b_var, T_execution_context)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : When we reach this step, {var} has already been removed from the execution context stack and {var} is the currently running execution context")
    def _(cond, env0, asserting):
        [vara, varb] = cond.children
        env0.assert_expr_is_of_type(vara, T_execution_context)
        env0.assert_expr_is_of_type(varb, T_execution_context)
        return (env0, env0)

# ------------------------------------------------------------------------------
#> The value of the Function component
#> of the running execution context
#> is also called the <dfn>active function object</dfn>.

    tbd['{VAL_DESC} : the active function object'] = a_subset_of(T_function_object_)

    @exprd.put(r"{EXPR} : the active function object")
    def _(expr, env0, _):
        [] = expr.children
        return (T_function_object_, env0)

# ------------------------------------------------------------------------------
#> <dfn>ECMAScript code execution contexts</dfn>
#> have the additional state components listed in
#> <emu-xref href="#table-additional-state-components-for-ecmascript-code-execution-contexts"></emu-xref>

    @exprd.put(r"{EXPR} : a new ECMAScript code execution context")
    def _(expr, env0, _):
        [] = expr.children
        return (T_execution_context, env0)

# ------------------------------------------------------------------------------
#> Execution contexts representing the evaluation of Generators
#> have the additional state components listed in
#> <emu-xref href="#table-additional-state-components-for-generator-execution-contexts"></emu-xref>.

    @condd.put(r"{CONDITION_1} : {var} does not have a Generator component")
    def _(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_execution_context)
        return (env0, env0)

# ------------------------------------------------------------------------------

    # 10.3.1
    @nv.put(r"{COMMAND} : Perform any necessary implementation-defined initialization of {var}.")
    def _(anode, env0):
        [var] = anode.children
        env0.assert_expr_is_of_type(var, T_execution_context)
        return env0

    # 15.10.3
    @condd.put(r"{CONDITION_1} : The current execution context will not subsequently be used for the evaluation of any ECMAScript code or built-in functions. The invocation of Call subsequent to the invocation of this abstract operation will create and push a new execution context before performing any such evaluation")
    def _(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

    # 15.10.3
    @nv.put(r"{COMMAND} : Discard all resources associated with the current execution context.")
    def _(anode, env0):
        [] = anode.children
        return env0

# ==============================================================================
#@ 9.5 Jobs and Host Operations to Enqueue Jobs

if 1:
    tbd['{VAL_DESC} : a Job Abstract Closure'] = T_Job
    tbd['{VAL_DESC} : a JobCallback Record'] = T_JobCallback_Record

# ==============================================================================
#@ 9.6 InitializeHostDefinedRealm

if 1:
    @condd.put(r"{CONDITION_1} : the host requires use of an exotic object to serve as {var}'s global object")
    def _(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_Realm_Record)
        return (env0, env0)

    @condd.put(r"{CONDITION_1} : the host requires that the `this` binding in {var}'s global scope return an object other than the global object")
    def _(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_Realm_Record)
        return (env0, env0)

    @nv.put(r"{COMMAND} : Create any host-defined global object properties on {var}.")
    def _(anode, env0):
        [var] = anode.children
        env0.assert_expr_is_of_type(var, T_Object)
        return env0

# ==============================================================================
#@ 9.7 Agents

#> While an agent's executing thread executes jobs,
#> the agent is the <dfn>surrounding agent</dfn>
#> for the code in those jobs.

if 1:
    @exprd.put(r'{EXPR} : the Agent Record of the surrounding agent')
    @exprd.put(r"{EXPR} : the surrounding agent's Agent Record")
    def _(expr, env0, _):
        [] = expr.children
        return (T_Agent_Record, env0)

    @condd.put(r"{CONDITION_1} : This call to Evaluate is not happening at the same time as another call to Evaluate within the surrounding agent")
    def _(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

#> An <dfn>agent signifier</dfn> is a globally-unique opaque value
#> used to identify an Agent.

if 1:
    tbd['{VAL_DESC} : an agent signifier'] = T_agent_signifier_
    tbd['{LIST_ELEMENTS_DESCRIPTION} : agent signifiers'] = T_agent_signifier_

    @condd.put(r"{NUM_COMPARISON} : {NUM_COMPARAND} is equivalent to {NUM_COMPARAND}")
    def _(cond, env0, asserting):
        [a, b] = cond.children
        env0.assert_expr_is_of_type(a, T_agent_signifier_)
        env0.assert_expr_is_of_type(b, T_agent_signifier_)
        return (env0, env0)

# ==============================================================================
#@ 9.10 Processing Model of WeakRef and FinalizationRegistry Objects

if 1:
    # 9.10.4.1
    @nv.put(r"{SMALL_COMMAND} : perform any host-defined steps for reporting the error")
    def _(anode, env0):
        [] = anode.children
        return env0

# ==============================================================================
#@ 9.13 CleanupFinalizationRegistry

if 1:
    @nv.put(r"{COMMAND} : Choose any such {var}.")
    def _(anode, env0):
        [var] = anode.children
        return env0.ensure_expr_is_of_type(var, T_FinalizationRegistryCellRecord_)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 10 Ordinary and Exotic Objects Behaviours

# ==============================================================================
#@ 10.1 Ordinary Object Internal Methods and Internal Slots

set_up_internal_thing('slot', 'Prototype',  T_Object | T_Null)
set_up_internal_thing('slot', 'Extensible', T_Boolean)

# ==============================================================================
#@ 10.2 ECMAScript Function Objects

if 1:
    tbd['{VAL_DESC} : an ECMAScript function object'] = a_subset_of(T_function_object_)
    tbd['{VAL_DESC} : an ECMAScript function'] = a_subset_of(T_function_object_)

    # 10.2.4
    @condd.put(r"{CONDITION_1} : {DOTTING} exists and has been initialized")
    def _(cond, env0, asserting):
        [dotting] = cond.children
        return (env0, env0)

# ==============================================================================
#@ 10.3 Built-in Function Objects

if 1:
    tbd['{VAL_DESC} : a built-in function object'] = a_subset_of(T_function_object_)

set_up_internal_thing('slot', 'InitialName', T_Null | T_String)

if 1:
    @exprd.put(r"{EX} : *this* value")
    @exprd.put(r"{EX} : the *this* value")
    def _(expr, env0, _):
        return (T_Tangible_, env0)

    @exprd.put(r"{EX} : NewTarget")
    def _(expr, env0, _):
        [] = expr.children
        return (T_constructor_object_ | T_Undefined, env0)

    # 10.3.1
    @exprd.put(r"{EXPR} : the Completion Record that is the result of evaluating {var} in a manner that conforms to the specification of {var}. {var} is the *this* value, {var} provides the named parameters, and the NewTarget value is *undefined*")
    def _(expr, env0, _):
        [avar, bvar, cvar, dvar] = expr.children
        assert avar.children == bvar.children
        env0.assert_expr_is_of_type(avar, T_function_object_)
        env0.assert_expr_is_of_type(cvar, T_Tangible_)
        env0.assert_expr_is_of_type(dvar, ListType(T_Tangible_))
        return (T_Tangible_ | T_throw_, env0)

    # 10.3.2
    @exprd.put(r"{EXPR} : the Completion Record that is the result of evaluating {var} in a manner that conforms to the specification of {var}. The *this* value is uninitialized, {var} provides the named parameters, and {var} provides the NewTarget value")
    def _(expr, env0, _):
        [avar, bvar, cvar, dvar] = expr.children
        assert avar.children == bvar.children
        env0.assert_expr_is_of_type(avar, T_function_object_)
        env0.assert_expr_is_of_type(cvar, ListType(T_Tangible_))
        env0.assert_expr_is_of_type(dvar, T_Tangible_)
        return (T_Tangible_ | T_throw_, env0)

    # 10.3.3
    @exprd.put(r"{EXPR} : a List containing the names of all the internal slots that {h_emu_xref} requires for the built-in function object that is about to be created")
    def _(expr, env0, _):
        [xref] = expr.children
        return (ListType(T_SlotName_), env0)

    # 10.3.3
    tbd['{VAL_DESC} : some other definition of a function\'s behaviour provided in this specification'] = T_alg_steps
    tbd['{VAL_DESC} : a set of algorithm steps'] = T_alg_steps

# ==============================================================================
#@ 10.4.1 Bound Function Exotic Objects

tbd['{VAL_DESC} : a bound function exotic object'] = T_bound_function_exotic_object_

# ==============================================================================
#@ 10.4.2 Array Exotic Objects

if 1:
    tbd['{VAL_DESC} : an Array exotic object'] = T_Array_object_
    tbd['{VAL_DESC} : an Array'] = T_Array_object_

# ==============================================================================
#@ 10.4.3 String Exotic Objects

if 1:
    tbd['{VAL_DESC} : a String exotic object'] = T_String_exotic_object_

# ==============================================================================
#@ 10.4.4 Arguments Exotic Objects

if 1:
    tbd['{VAL_DESC} : an arguments exotic object'] = a_subset_of(T_Object)

set_up_internal_thing('slot', 'ParameterMap', T_Object)

if 1:
    # 10.4.4.{2,4}
    @condd.put(r"{CONDITION_1} : The following Set will succeed, since formal parameters mapped by arguments objects are always writable")
    def _(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

    # 10.4.4.3
    @condd.put(r"{CONDITION_1} : {var} contains a formal parameter mapping for {var}")
    def _(cond, env0, asserting):
        [avar, bvar] = cond.children
        env0.assert_expr_is_of_type(avar, T_Object)
        env0.assert_expr_is_of_type(bvar, T_String | T_Symbol)
        return (env0, env0)

# ==============================================================================
#@ 10.4.5 Integer-Indexed Exotic Objects

if 1:
    tbd['{VAL_DESC} : an Integer-Indexed exotic object'] = T_Integer_Indexed_object_

set_up_internal_thing('slot', 'ViewedArrayBuffer', T_ArrayBuffer_object_ | T_SharedArrayBuffer_object_)
set_up_internal_thing('slot', 'ArrayLength',       T_MathInteger_)
set_up_internal_thing('slot', 'ByteOffset',        T_MathInteger_)
set_up_internal_thing('slot', 'ContentType',       T_tilde_BigInt_ | T_tilde_Number_)
set_up_internal_thing('slot', 'TypedArrayName',    T_String)
set_up_internal_thing('slot', 'ByteLength',        T_MathInteger_)

# ==============================================================================
#@ 10.4.6 Module Namespace Exotic Objects

if 1:
    tbd['{VAL_DESC} : a module namespace exotic object'] = T_Object

# ==============================================================================
# 10.5 Proxy Object Internal Methods and Internal Slots

if 1:
    tbd['{VAL_DESC} : a Proxy exotic object'] = T_Proxy_exotic_object_
    tbd['{VAL_DESC} : a Proxy object'] = T_Proxy_exotic_object_

set_up_internal_thing('slot', 'ProxyHandler', T_Object | T_Null)
set_up_internal_thing('slot', 'ProxyTarget',  T_Object | T_Null)

main()

# vim: sw=4 ts=4 expandtab
