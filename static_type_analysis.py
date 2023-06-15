#!/usr/bin/python3

# ecmaspeak-py/static_type_analysis.py:
# Perform static type analysis/inference on the spec's pseudocode.
#
# Copyright (C) 2018  J. Michael Dyck <jmdyck@ibiblio.org>

import re, atexit, time, sys, pdb
from collections import OrderedDict, defaultdict
from itertools import zip_longest
from pprint import pprint
from dataclasses import dataclass, field as dataclass_field
from typing import FrozenSet, Set, Tuple

import shared, HTML
from shared import stderr, spec, DL
from Pseudocode_Parser import ANode
from Graph import Graph
from DecoratedFuncDict import DecoratedFuncDict
import records

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

outdir = sys.argv[1]
shared.register_output_dir(outdir)
spec.restore()

def main():
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
    # and create a HierType and a TNode for each.
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

        # until PR #3063 is merged:
        if (mo := re.fullmatch(r'this(\w+)Value', self.name)):
            foo = mo.group(1)
            return_type = T_IntegralNumber_ | T_NaN_Number_ if foo == 'Time' else HierType(foo)
            self.initial_return_type = NormalCompletionType(return_type) | ThrowCompletionType(T_TypeError)

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
            assert self.return_type in [T_Completion_Record, T_TBD]
            tnt = NormalCompletionType(T_Tangible_ | T_tilde_empty_ | T_Reference_Record) | T_abrupt_completion
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
                discriminator = HierType(alg_defn.discriminator)
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
                (abrupt_part, normal_part) = rt.split_by(T_abrupt_completion)

            if normal_part.is_a_subtype_of_or_equal_to(T_normal_completion):
                normal_value_type = s_dot_field(normal_part, '[[Value]]')
            else:
                normal_value_type = normal_part

            iput_name_and_type('normal', normal_value_type)
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

        parameter_names = set()

        if self.for_param_name is not None:
            assert self.for_param_type is not None
            e.vars[self.for_param_name] = self.for_param_type
            parameter_names.add(self.for_param_name)

        for (pn, pt) in self.parameter_types.items():
            assert isinstance(pt, Type)
            e.vars[pn] = pt
            parameter_names.add(pn)

        e.vars['*return*'] = self.return_type

        if self.species.startswith('bif:'):
            expected_return_type = NormalCompletionType(T_Tangible_) | T_throw_completion
            # T_tilde_empty_ shouldn't really be allowed,
            # but if I leave it out,
            # I get a bunch of complaints that I think are false positives.
        else:
            expected_return_type = self.return_type

        # An algorithm must either *always* return completion records
        # or *never* return completion records.

        (cr_part_of_type, noncr_part_of_type) = expected_return_type.split_by(T_Completion_Record)
        if cr_part_of_type != T_0 and noncr_part_of_type != T_0:
            stderr("")
            stderr(f"!!! In header for {op_name}, the return type has")
            stderr(f"both   cr_part_of_type: {cr_part_of_type}")
            stderr(f"and noncr_part_of_type: {noncr_part_of_type}")
            stderr("")
            sys.exit(1)
        elif cr_part_of_type != T_0:
            returns_completion_records = True
        elif noncr_part_of_type != T_0:
            returns_completion_records = False
        else:
            assert 0

        e.parret = ParRet(parameter_names, expected_return_type, returns_completion_records)

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
                                tnode = tnode_for_type_[a]
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
            file=split_types_f)

        result = (inside_B, outside_B)
        split_memo[(A,B)] = result
        return result


def member_is_a_subtype_or_equal(A, B):
    assert not isinstance(A, UnionType); assert A != T_TBD
    assert not isinstance(B, UnionType); assert B != T_TBD

    if A == B: return True

    if isinstance(A, HierType):
        if isinstance(B, HierType):
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
    type = HierType(type_name)
    if optionality: type = type | T_not_in_node
    return type

# ------------------------------------------------------------------------------

named_type_hierarchy = {
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

tnode_for_type_ = {}

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

        tnode_for_type_[type] = self

def HierType_etc(type_name):
    assert isinstance(type_name, str)
    t = HierType(type_name)
    variable_name = 'T_' + type_name.replace(' ', '_').replace('-', '_')
    globals()[variable_name] = t
    return t

def traverse(typesdict, p):
    for (type_name, subtypesdict) in typesdict.items():
    # sorted(typesdict.items(), key=lambda tup: 1 if tup[0] == 'List' else 0):
        type = HierType_etc(type_name)
        tnode = TNode(type, p)
        traverse(subtypesdict, tnode)

stderr("initializing the type hierarchy...")
traverse(named_type_hierarchy, None)

troot = tnode_for_type_[T_Top_]

# ------------------------------------------------------------------------------

# The spec declares Module Record with only one sub-schema, Cyclic Module Record.
# And it declares Cyclic Module Record with only one sub-schema, Source Text Module Record.
# But letting that stand causes problems for STA,
# because it assumes you can replace a union-of-all-subtypes with the supertype,
# but we don't want to replace (e.g.) Cyclic Module Record with Module Record.
# The spec assumes that other specs/implementations can define
# other sub-schemas of [Cyclic] Module Record,
# so we create some ad hoc sub-schemas to prevent the union-of-all-subtypes mistake.
rs = records.RecordSchema('other Module Record', 'Module Record')
rs = records.RecordSchema('other Cyclic Module Record', 'Cyclic Module Record')

def traverse_record_schema(super_schema, super_tnode):
    for sub_schema in super_schema.sub_schemas:
        if sub_schema.tc_schema_name == 'Completion Record':
            # Don't create HierType('Completion Record'),
            # because that would complicate things.
            # Instead, we create T_Completion_Record as a RecordType.
            continue
        sub_type = HierType_etc(sub_schema.tc_schema_name)
        sub_tnode = TNode(sub_type, super_tnode)
        traverse_record_schema(sub_schema, sub_tnode)

traverse_record_schema(spec.root_RecordSchema, tnode_for_type_[T_Record])

# ------------------------------------------------------------------------------

# Define tilde-types

# The spec doesn't have a form for 'declaring' tilde-words,
# so all you can do is look for uses of them.
# There are various places that tilde-words appear,
# but it turns out you can find all the distinct ones
# by looking for them just in algorithms.

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
        continue # For now, it's clearer if it appears in the named_type_hierarchy
    elif re.fullmatch(r'~\w+(8|8C|16|32|64)~', tilde_word):
        parent_type = T_TypedArray_element_type
    else:
        parent_type = T_tilde_
    parent_tnode = tnode_for_type_[parent_type]

    tilde_type_name = 'tilde' + re.sub('\W', '_', tilde_word)
    type = HierType_etc(tilde_type_name)
    tnode = TNode(type, parent_tnode)

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

def convert_nature_node_to_type(nature_node):
    if nature_node is None: return T_TBD

    (_, sup_t) = type_bracket_for(nature_node, None)
    return sup_t

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
        union_of_list_memtypes(list_memtypes)
        + union_of_record_memtypes(record_memtypes)
        + union_of_proc_memtypes(proc_memtypes)
        + union_of_hier_memtypes(hier_memtypes)
    )

    assert result_memtypes

    if len(result_memtypes) == 1:
        result = list(result_memtypes)[0]
    else:
        result = UnionType(frozenset(result_memtypes))

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

def union_of_record_memtypes(record_memtypes):

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

def union_of_proc_memtypes(proc_memtypes):

    if len(proc_memtypes) <= 1:
        return proc_memtypes

    assert 0

# ------------------------------------------------------------------------------

def union_of_hier_memtypes(memtypes):

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

T_0 = UnionType(frozenset())

T_TBD = TBDType()

def CompletionType(Type_field_stype):
    return RecordType('Completion Record', (('[[Type]]', Type_field_stype),))

T_break_completion    = CompletionType(T_tilde_break_)
T_continue_completion = CompletionType(T_tilde_continue_)
T_return_completion   = CompletionType(T_tilde_return_)
T_throw_completion    = CompletionType(T_tilde_throw_)

T_abrupt_completion = T_continue_completion | T_break_completion | T_return_completion | T_throw_completion

T_character_ = T_code_unit_ | T_code_point_

T_MathNonNegativeInteger_ = T_MathInteger_ # for now

T_MatcherContinuation = ProcType((T_MatchState,                      ), T_MatchResult)
T_Matcher             = ProcType((T_MatchState, T_MatcherContinuation), T_MatchResult)
T_RegExpMatcher_  = ProcType((ListType(T_character_), T_MathNonNegativeInteger_), T_MatchResult)
T_Job             = ProcType((                       ), T_Tangible_ | T_tilde_empty_ | T_throw_completion)

T_ReadModifyWrite_modification_closure = ProcType((ListType(T_MathInteger_), ListType(T_MathInteger_)), ListType(T_MathInteger_))

T_captures_entry_ = T_CaptureRange | T_Undefined
T_captures_list_  = ListType(T_captures_entry_)

T_Unicode_code_points_ = ListType(T_code_point_)

T_Integer_Indexed_object_ = T_TypedArray_object_

T_Shared_Data_Block_Event = T_ReadSharedMemory_Event | T_WriteSharedMemory_Event | T_ReadModifyWriteSharedMemory_Event

T_Event = T_Shared_Data_Block_Event | T_Synchronize_Event | T_Host_Specific_Event

# ------------------------------------------------------------------------------

type_tweaks_tuples = [
    ('MV'                                       , '*return*'               , T_TBD                 , T_MathInteger_),
    ('PromiseResolve'                           , '_C_'                    , T_constructor_object_ , T_Object),
    ('Day'                                      , '_t_'                    , T_TBD                 , T_IntegralNumber_ ),
    ('TimeWithinDay'                            , '_t_'                    , T_TBD                 , T_IntegralNumber_ ),
    ('DaysInYear'                               , '_y_'                    , T_TBD                 , T_IntegralNumber_ ),
    ('DayFromYear'                              , '_y_'                    , T_TBD                 , T_IntegralNumber_ ),
    ('TimeFromYear'                             , '_y_'                    , T_TBD                 , T_IntegralNumber_ ),
    ('YearFromTime'                             , '_t_'                    , T_TBD                 , T_IntegralNumber_ ),
    ('InLeapYear'                               , '_t_'                    , T_TBD                 , T_IntegralNumber_ ),
    ('MonthFromTime'                            , '_t_'                    , T_TBD                 , T_IntegralNumber_ ),
    ('DayWithinYear'                            , '_t_'                    , T_TBD                 , T_IntegralNumber_ ),
    ('DateFromTime'                             , '_t_'                    , T_TBD                 , T_IntegralNumber_ ),
    ('WeekDay'                                  , '_t_'                    , T_TBD                 , T_IntegralNumber_ ),
    ('HourFromTime'                             , '_t_'                    , T_TBD                 , T_IntegralNumber_ ),
    ('MinFromTime'                              , '_t_'                    , T_TBD                 , T_IntegralNumber_ ),
    ('SecFromTime'                              , '_t_'                    , T_TBD                 , T_IntegralNumber_ ),
    ('msFromTime'                               , '_t_'                    , T_TBD                 , T_IntegralNumber_ ),
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

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

class Env:
    def __init__(self, outer=None):
        self.parret = None
        self.vars = {}
        self.outer = outer

    def __str__(self):
        return str(self.vars)

    def copy(self):
        e = Env(self.outer)
        e.parret = self.parret
        e.vars = self.vars.copy()
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

    def plus_new_entry(self, var, t, shadowing_outer_is_okay=False):
        if isinstance(var, str):
            var_name = var
        elif isinstance(var, ANode):
            var_name = var.source_text()
        else:
            assert 0

        if var_name in self.vars:
            add_pass_error(
                var,
                "re-Let on existing var `%s`. Use Set?" % var_name
            )
            var_t = self.vars[var_name]
            if t == var_t:
                # but at least we're not changing the type
                return self

            elif t == T_TBD:
                return self
                add_pass_error(
                    var,
                    "... also, ignoring the attempt to change the type of var to %s" % str(t)
                )

            elif var_name in ['_v_', '_value_'] and var_t in [T_Normal, T_Tangible_ | T_not_set] and t == T_Undefined:
                # IteratorBindingInitialization, IteratorDestructuringAssignmentEvaluation, others?:
                # This isn't a re-Let,
                # because it's never the case that _v_ is already defined at this point,
                # but my STA isn't smart enough to know that.
                add_pass_error(
                    var,
                    "... actually, it isn't, but STA isn't smart enough"
                )
                return self

            elif t.is_a_subtype_of_or_equal_to(var_t):
                add_pass_error(
                    var,
                    "... also, this narrows the type of var from %s to %s" % (var_t, t)
                )
                return self.with_expr_type_narrowed(var, t)

            else:
                add_pass_error(
                    var,
                    "... also, this changes the type of var from %s to %s" % (var_t, t)
                )
                return self.with_expr_type_replaced(var, t)

        if not shadowing_outer_is_okay and (
            self.outer is not None and var_name in self.outer.vars
            or
            self.outer is not None and self.outer.outer is not None and var_name in self.outer.outer.vars

            # Currently, the spec has a few examples of
            # an Abstract Closure within an Abstract Closure:
            # - ContinueDynamicImport
            # - CompilePattern
            # - CompileSubpattern
            # - CompileAssertion
            # - CompileAtom
            # - Promise.prototype.finally
            # but no deeper nesting,
            # so we don't need to go past self.outer.outer.
        ):
            add_pass_error(
                var,
                f"re-use of outer var `{var_name}`"
            )
            # but still add the entry

        assert isinstance(t, Type)
        e = self.copy()
        e.vars[var_name] = t
        return e

    def with_var_removed(self, var):
        var_name = var.source_text()
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
        (_, result_env) = self.ensure_expr_is_of_type_(expr, expected_t)
        return result_env

    def ensure_expr_is_of_type_(self, expr, expected_t):
        assert expected_t != T_TBD

        (expr_type, expr_env) = tc_expr(expr, self)

        if expr_type == T_TBD:
            resulting_expr_type = expected_t
            result_env = expr_env.with_expr_type_replaced(expr, resulting_expr_type)

        elif expr_type.is_a_subtype_of_or_equal_to(expected_t):
            # great!
            resulting_expr_type = expr_type
            result_env = expr_env

        else:
            expr_text = expr.source_text()
            add_pass_error_re_wrong_type(expr, expr_type, expected_t)
            if expr_text == '*null*':
                # Don't try to change the type of *null*!
                assert 0
                resulting_expr_type = expr_type
                result_env = expr_env
            elif expr_text == '*undefined*':
                resulting_expr_type = expr_type
                result_env = expr_env
            elif expr_text == '« »':
                resulting_expr_type = expr_type
                result_env = expr_env
            else:
                resulting_expr_type = expected_t
                # or you could split {expr_type} by {expected_t}
                result_env = expr_env.with_expr_type_replaced(expr, resulting_expr_type)
        return (resulting_expr_type, result_env)

    def ensure_A_can_be_element_of_list_B(self, item_ex, list_ex):
        (list_type, list_env) = tc_expr(list_ex, self)
        (item_type, item_env) = tc_expr(item_ex, list_env)

        if (list_type == T_List or list_type == ListType(T_TBD)) and item_type == T_TBD:
            # shrug
            result = item_env

        # ----------------------------------------
        # cases where we change the ST of list_ex:

        elif list_type == T_List or list_type == ListType(T_TBD) or list_type == T_TBD or list_type == ListType(T_0):
            result = item_env.with_expr_type_replaced( list_ex, ListType(item_type))

        elif list_type == ListType(T_String) and item_type == T_Symbol:
            expected_list_type = ListType(T_String | T_Symbol)
            add_pass_error_re_wrong_type(list_ex, list_type, expected_list_type)
            result = item_env.with_expr_type_replaced( list_ex, expected_list_type)

        elif list_type == ListType(T_PromiseReaction_Record) | T_Undefined and item_type == T_PromiseReaction_Record:
            result = item_env.with_expr_type_narrowed(list_ex, ListType(T_PromiseReaction_Record))

        elif list_type == ListType(T_Match_Record) and item_type == T_Undefined and list_ex.source_text() == '_indices_':
            expected_list_type = ListType(T_Match_Record | T_Undefined)
            add_pass_error_re_wrong_type(list_ex, list_type, expected_list_type)
            result = item_env.with_expr_type_replaced(list_ex, expected_list_type)

        # ----------------------------------------
        # cases where we change the ST of item_ex:

        elif item_type == T_TBD:
            result = item_env.with_expr_type_replaced(item_ex, list_type.element_type)

        elif list_type == ListType(T_String) and item_type == T_String | T_Null:
            # ParseModule
            add_pass_error_re_wrong_type(item_ex, item_type, T_String)
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
        expr_text = expr.source_text()
        e = self.copy()
        e.vars[expr_text] = new_t
        return e

    def set_A_to_B(self, settable, expr):
        (expr_type,     env1) = tc_expr(expr,     self)
        (settable_type, env2) = tc_expr(settable, env1)

        # Analyze {expr} before {settable}
        # because the analysis of {expr}
        # might tell you something about the type of {settable}
        # *before* the 'Set' occurs.

        if settable.source_text() in self.parret.parameter_names:
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

        if expr_t == T_0:
            # As far as {self} is concerned,
            # execution cannot reach {expr}.
            return (None, None)

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
                # or Evaluation of "YieldExpression : `yield` `*` AssignmentExpression",
                # the first time through the Repeat loop

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
        e = Env(self.outer)
        e.parret = self.parret
        for (vn, vt) in self.vars.items():
            if vn in header_names:
                e.vars[vn] = vt
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

    e = Env(envs[0].outer)
    e.parret = envs[0].parret
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

    e = Env(envs[0].outer)
    e.parret = envs[0].parret

    for env in envs:
        assert env.outer is e.outer
        assert env.parret is e.parret

    all_vars = set()
    for env in envs:
        for var_name in env.vars.keys():
            all_vars.add(var_name)

    for var_name in sorted(all_vars):
        e.vars[var_name] = union_of_types([
            env.vars[var_name] if var_name in env.vars else T_not_set
            for env in envs
        ])

    return e

# ------------------------------------------------------------------------------

@dataclass
class ParRet:
    # 'ParRet' is short for 'Parameters & Return'.
    # It's a structure (referenced by every Env)
    # that holds data relating to the parameters & returns
    # of the algorithm or abstract closure
    # currently under analysis.

    parameter_names: Set[str]
    expected_return_type: Type
    returns_completion_records: bool
    return_envs: Set[Env] = dataclass_field(default_factory=set)

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

def add_pass_error_re_wrong_type(expr, expr_t, expected_t):
    add_pass_error(
        expr,
        f"{expr.source_text()} has type {expr_t}, but this context expects that it be of type {expected_t}"
    )

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

    final_env = tc_proc(tah.name, tah.t_defns, init_env)

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

                # No, only convey that STA wants to change the type if it's the return-type.
                # (And even that is questionable.)
                if pn != '*return*': continue

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

def tc_proc(op_name, defns, init_env):
    assert defns

    header_names = sorted(init_env.vars.keys())

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
            assert isinstance(discriminator, HierType)
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

    rr_envs = []
    for return_env in init_env.parret.return_envs:
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
    parret = env_at_return_point.parret

    if trace_this_op:
        print("Type of returned value:", type_of_returned_value)
        input('hit return to continue ')
        if T_abrupt_completion.is_a_subtype_of_or_equal_to(type_of_returned_value):
            input('hit return to continue ')
        # if T_throw_completion.is_a_subtype_of_or_equal_to(type_of_returned_value):
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

    #> In algorithms within abstract operations which are declared to return a Completion Record,
    #> and within all built-in functions,
    #> the returned value is first passed to NormalCompletion,
    #> and the result is used instead.
    #> This rule does not apply within the Completion algorithm
    #> or when the value being returned is clearly marked as a Completion Record in that step;
    #> these cases are:
    #>  - when the result of applying Completion, NormalCompletion, or ThrowCompletion is directly returned
    #>  - when the result of constructing a Completion Record is directly returned

    if parret.returns_completion_records:
        (cr_part_of_type, noncr_part_of_type) = type_of_returned_value.split_by(T_Completion_Record)
        if noncr_part_of_type != T_0:
           type_of_returned_value = NormalCompletionType(noncr_part_of_type) | cr_part_of_type 

    # Check that the return value conforms to the proc's declared return
    if not type_of_returned_value.is_a_subtype_of_or_equal_to(parret.expected_return_type):
        add_pass_error(
            node,
            f"static type of return value is {type_of_returned_value}, should be (a subtype of) {parret.expected_return_type}"
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

            if pn == '*return*' and T_not_returned.is_a_subtype_of_or_equal_to(ptype) and ptype != T_abrupt_completion | ListType(T_code_unit_) | T_Reference_Record | T_Tangible_ | T_tilde_empty_ | T_not_returned:
                add_pass_error(
                    node,
                    "At exit, ST of `%s` is `%s`" % (pn, ptype)
                )

    parret.return_envs.add(aug_env)

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

    s_nv = lookup_for_prod(p, 's_nv')
    result = s_nv(anode, env0)

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

    s_cond = lookup_for_prod(p, 's_cond')
    result = s_cond(cond, env0, asserting)

    assert isinstance(result, tuple)
    assert len(result) == 2
    assert isinstance(result[0], Env) or result[0] is None
    assert isinstance(result[1], Env) or result[1] is None

    if trace_this_op:
        print()
        print("Leaving c:", p)
        print("          ", cond.source_text())
        mytrace(result[0])

    return result

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

    result = lookup_for_prod(vd_p, 's_tb')

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

# ------------------------------------------------------------------------------

def convert_nature_to_type(nature):
    fake_p = '{VAL_DESC} : ' + nature
    tb = lookup_for_prod(fake_p, 's_tb', False)
    if tb:
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
            'an event in SharedDataBlockEventSet(_execution_)': T_Shared_Data_Block_Event,

            # for phrase:
            'Parse Node': T_Parse_Node,

            'an immutable prototype exotic object': T_Object,

            'an execution': T_Candidate_Execution_Record, # ???

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
        s_expr = lookup_for_prod(p, 's_expr')

        (expr_type, env1) = s_expr(expr, env0, expr_value_will_be_discarded)

        assert isinstance(expr_type, Type)
        assert isinstance(env1, Env)

        if expr_type in [T_Top_, T_TBD, T_0]:
            add_pass_error(
                expr,
                "warning: expr `%s` has type %s" % (expr_text, expr_type)
            )

        (cr_part_of_type, noncr_part_of_type) = expr_type.split_by(T_Completion_Record)
        if cr_part_of_type != T_0 and noncr_part_of_type != T_0:
            if expr_text.endswith('.[[EvaluationError]]'):
                assert expr_type == T_throw_completion | T_tilde_empty_
                # It's just declared that way.
            else:
                add_pass_error(
                    expr,
                    f"warning: expr `{expr_text}` has type {expr_type}, which mixes completions and non-completions"
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

# ------------------------------------------------------------------------------

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
        assert T_abrupt_completion.is_a_subtype_of_or_equal_to(rt)
        mast = main_arg.source_text()

        if mast in [
            '|FunctionStatementList|',
        ]:
            # Might return a throw|return completion, but not continue|break
            (_, narrowed_rt) = rt.split_by(T_continue_completion | T_break_completion)
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
            (_, narrowed_rt) = rt.split_by(T_continue_completion | T_break_completion | T_return_completion)
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
        '~normal~'  : T_normal_completion,
        '~continue~': T_continue_completion,
        '~break~'   : T_break_completion,
        '~return~'  : T_return_completion,
        '~throw~'   : T_throw_completion,
        'either ~return~ or ~throw~': T_return_completion | T_throw_completion,
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
                    # This condition, by focusing on T_throw_completion, is over-specific,
                    # but I'm guessing it catches the common cases.
                    T_throw_completion.is_a_subtype_of_or_equal_to(arg_type)
                    and
                    not T_throw_completion.is_a_subtype_of_or_equal_to(pt)
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
        dsbn_name = dsbn.source_text()
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
    # Add info for named record types
    # by calling process_declared_record_type_info().

    #? # 2651: Table 8: Completion Record Fields
    #? 'Completion Record': {
    #?     '[[Type]]'   : T_completion_kind_,
    #?     '[[Value]]'  : T_Tangible_ | T_tilde_empty_,
    #?     '[[Target]]' : T_String | T_tilde_empty_,
    #? },

}

def process_declared_record_type_info():
    for record_schema in spec.RecordSchema_for_name_.values():

        d_from_spec = {}
        schemas = reversed([* record_schema.self_and_supers() ])
        for schema in schemas:
            for field_decl in schema.addl_field_decls.values():
                if field_decl.value_description is None:
                    t = convert_nature_to_type(field_decl.nature)
                else:
                    t = convert_nature_node_to_type(field_decl.value_description)
                d_from_spec[field_decl.name] = t

        ffrtn_name = record_schema.tc_schema_name
        # At this point, I used to map
        # from the title-case schema name in spec.RecordSchema_for_name_
        # to the name that the spec uses in practice (e.g., in {VAL_DESC}).

        assert ffrtn_name not in fields_for_record_type_named_
        fields_for_record_type_named_[ffrtn_name] = d_from_spec

    def tweak_record_schema_field_type(schema_name, field_name, t_from_spec, t_for_compat):
        fields_dict = fields_for_record_type_named_[schema_name]
        assert fields_dict[field_name] == t_from_spec
        fields_dict[field_name] = t_for_compat

    tweak_record_schema_field_type(
        'JobCallback Record', '[[HostDefined]]',
        T_host_defined_,
        T_host_defined_ | T_tilde_empty_
    )

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

def set_up_internal_thing(method_or_slot, thing_name, stype):
    # Ignore `method_or_slot`
    if thing_name in type_of_internal_thing_:
        # [[GeneratorBrand]] is declared for both
        # Generator Instances and AsyncGenerator Instances.
        assert thing_name == '[[GeneratorBrand]]', thing_name

        t = type_of_internal_thing_[thing_name]
        assert t == stype
    else:
        type_of_internal_thing_[thing_name] = stype

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
        return_type = NormalCompletionType(return_type) | T_throw_completion

        t = ProcType(tuple(param_types), return_type)

    elif method_or_slot == 'slot':
        field_value_type = row.cell_nodes[1]._syntax_tree
        value_description = field_value_type.children[0]
        t = convert_nature_node_to_type(value_description)

        if thing_name in ['[[PromiseFulfillReactions]]', '[[PromiseRejectReactions]]']:
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

    set_up_internal_thing(method_or_slot, thing_name, t)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

class_for_prod_str_ = DecoratedFuncDict()

def lookup_for_prod(prod_str, attr_name, must_exist=True):
    try:
        cls = class_for_prod_str_[prod_str]
    except KeyError:
        if must_exist:
            stderr()
            stderr('!' * 40)
            stderr("Need:")
            stderr(f"@P({prod_str!r})")
            stderr()
            sys.exit(1)
        else:
            return None

    if hasattr(cls, attr_name):
        return getattr(cls, attr_name)
    else:
        if must_exist:
            stderr()
            stderr('!' * 40)
            stderr("For:")
            stderr(f"@P({prod_str!r})")
            stderr(f"the class needs attr: {attr_name}")
            stderr()
            sys.exit(1)
        else:
            return None

P = class_for_prod_str_.put

def s_nv_pass_down(anode, env0):
    [child] = anode.children
    return tc_nonvalue(child, env0)

def s_expr_pass_down(expr, env0, expr_value_will_be_discarded):
    [child] = expr.children
    return tc_expr(child, env0, expr_value_will_be_discarded)

def s_tb_pass_down(vd, env):
    [child] = vd.children
    return type_bracket_for(child, env)

# Note that, in what follows,
# the classes declared as "class _"
# don't exist to be instantiated,
# they only exist as containers of attributes.

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# Unit productions (and other similar productions)
# where the semantics are just to delegate to a child node.

@P(r'{IND_COMMANDS} : {_indent_}{COMMANDS}{_outdent_}')
@P(r'{COMMANDS} : {_NL_N} {COMMAND}')
@P(r'{COMMAND} : {IF_CLOSED}')
@P(r'{COMMAND} : {IF_OTHER}')
@P(r'{ELSE_PART} : Else, {SMALL_COMMAND}.')
@P(r'{ELSE_PART} : Else,{IND_COMMANDS}')
@P(r'{ELSE_PART} : Otherwise, {SMALL_COMMAND}.')
@P(r"{COMMAND} : Perform the following substeps in an implementation-defined order, possibly interleaving parsing and error detection:{IND_COMMANDS}")
@P(r"{COMMAND} : Optionally, {SMALL_COMMAND}.")
@P(r"{ONE_LINE_ALG} : {_indent_}{nlai}{COMMAND}{_outdent_}{nlai}")
class _:
    s_nv = s_nv_pass_down

@P('{VALUE_DESCRIPTION} : {VAL_DESC}')
@P('{VAL_DESC} : {LITERAL}')
class _:
    s_tb = s_tb_pass_down

@P(r"{EXPR} : the result of {PP_NAMED_OPERATION_INVOCATION}")
@P(r"{EXPR} : {EX}")
@P(r"{EX} : ({EX})")
@P(r"{EX} : The value of {SETTABLE}")
@P(r"{EX} : the value of {SETTABLE}")
@P(r"{EX} : {code_point_lit}")
@P(r"{EX} : {LITERAL}")
@P(r"{EX} : {LOCAL_REF}")
@P(r"{EX} : {NUM_EXPR}")
@P(r"{EX} : {PAIR}")
@P(r"{EX} : {PP_NAMED_OPERATION_INVOCATION}")
@P(r"{EX} : {RECORD_CONSTRUCTOR}")
@P(r"{FACTOR} : ({NUM_EXPR})")
@P(r"{FACTOR} : {BIGINT_LITERAL}")
@P(r"{FACTOR} : {MATH_LITERAL}")
@P(r"{FACTOR} : {NUMBER_LITERAL}")
@P(r"{FACTOR} : {PP_NAMED_OPERATION_INVOCATION}")
@P(r"{FACTOR} : {SETTABLE}")
@P(r"{LOCAL_REF} : {PROD_REF}")
@P(r"{LOCAL_REF} : {SETTABLE}")
@P(r"{NAMED_OPERATION_INVOCATION} : {PREFIX_PAREN}")
@P(r"{NUM_COMPARAND} : {FACTOR}")
@P(r"{NUM_COMPARAND} : {SUM}")
@P(r"{NUM_COMPARAND} : {PRODUCT}")
@P(r"{NUM_EXPR} : {PRODUCT}")
@P(r"{NUM_EXPR} : {SUM}")
@P(r"{RHSS} : {RHS}")
@P(r"{SETTABLE} : {DOTTING}")
@P(r"{TERM} : {FACTOR}")
@P(r"{TERM} : {PRODUCT}")
@P(r"{TYPE_ARG} : {var}")
class _:
    s_expr = s_expr_pass_down

@P('{LITERAL} : {MATH_LITERAL}')
@P('{LITERAL} : {NUMBER_LITERAL}')
class _:
    s_tb = s_tb_pass_down
    s_expr = s_expr_pass_down

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# code point & code unit

# The spec doesn't define the terms 'code point' or 'code unit'.
# (It doesn't even refer to Unicode's definitions.)
# So there isn't an obvious place to handle pseudocode productions
# that relate to those terms. Instead, I'll put them here.
# (I considered 11.1 'Source Text' for 'code point',
# and 6.1.4 'The String Type' for 'code unit'.)

# ==============================================================================
# code point

@P('{VAL_DESC} : a Unicode code point')
class _:
    s_tb = T_code_point_

@P('{VAL_DESC} : a code point')
class _:
    s_tb = T_code_point_

@P('{VAL_DESC} : the single code point {code_point_lit} or {code_point_lit}')
class _:
    s_tb = a_subset_of(T_Unicode_code_points_)

@P('{VAL_DESC} : {backticked_oth}')
class _:
    s_tb = a_subset_of(T_Unicode_code_points_)

@P('{LIST_ELEMENTS_DESCRIPTION} : code points')
class _:
    s_tb = T_code_point_

@P(r'{code_point_lit} : ` [^`]+ ` \x20 U \+ [0-9A-F]{4} \x20 \( [A-Z -]+ \)')
@P(r'{code_point_lit} : \b U \+ [0-9A-F]{4} \x20 \( [A-Z -]+ \)')
class _:
    def s_expr(expr, env0, _):
        return (T_code_point_, env0)

@P(r'{CONDITION_1} : {var} has a numeric value less than {code_unit_lit}')
class _:
    def s_cond(cond, env0, asserting):
        [var, code_unit_lit] = cond.children
        env1 = env0.ensure_expr_is_of_type(var, T_code_point_) # odd
        return (env1, env1)

    # for 19.2.6.6
@P(r"{CONDITION_1} : {var} does not contain a valid UTF-8 encoding of a Unicode code point")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, ListType(T_MathInteger_))
        return (env0, env0)

@P(r"{EXPR} : the code point {var}")
        # This means "the code point whose numeric value is {var}"
@P(r"{EXPR} : the code point whose numeric value is {EX}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_MathInteger_)
        return (T_code_point_, env0)

@P(r"{CONDITION_1} : {var} has the same numeric value as a {h_emu_xref} or {h_emu_xref}")
class _:
    def s_cond(cond, env0, asserting):
        [var, emu_xref1, emu_xref2] = cond.children
        env0.assert_expr_is_of_type(var, T_code_point_)
        return (env0, env0)

@P(r"{EXPR} : the code point obtained by applying the UTF-8 transformation to {var}, that is, from a List of octets into a 21-bit value")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, ListType(T_MathInteger_))
        return (T_code_point_, env0)

@P(r"{EXPR} : the List of octets resulting by applying the UTF-8 transformation to {DOTTING}")
class _:
    def s_expr(expr, env0, _):
        [dotting] = expr.children
        env1 = env0.ensure_expr_is_of_type(dotting, T_code_point_)
        return (ListType(T_MathInteger_), env1)

# ----------

@P('{VAL_DESC} : a sequence of Unicode code points')
class _:
    s_tb = T_Unicode_code_points_

@P(r"{EXPR} : the empty sequence of Unicode code points")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_Unicode_code_points_, env0)

@P(r"{EX} : {backticked_word}")
class _:
    def s_expr(expr, env0, _):
        [backticked_word] = expr.children
        word = backticked_word.source_text()[1:-1]
        if word == 'General_Category':
            return (T_Unicode_code_points_, env0)
        elif word == 'u':
            return (T_code_point_, env0)
        else:
            assert 0, word

@P(r"{EX} : {backticked_oth}")
class _:
    def s_expr(expr, env0, _):
        [_] = expr.children
        return (T_Unicode_code_points_, env0)

@P(r"{CONDITION_1} : {var} contains any code point more than once")
@P(r"{CONDITION_1} : {var} contains any code points other than {backticked_word}, {backticked_word}, {backticked_word}, {backticked_word}, {backticked_word}, {backticked_word}, or {backticked_word}")
class _:
    def s_cond(cond, env0, asserting):
        [noi, *bw_] = cond.children
        env0.assert_expr_is_of_type(noi, T_Unicode_code_points_)
        for bw in bw_:
            assert len(bw.source_text()) == 3 # single-character 'words'
        return (env0, env0)

@P(r"{EXPR} : the List of Unicode code points {var}")
class _:
    def s_expr(expr, env0, _):
        [v] = expr.children
        env0.assert_expr_is_of_type(v, ListType(T_code_point_))
        return (ListType(T_code_point_), env0)

# ==============================================================================
# code unit

# (We can infer that it means "a UTF-16 code unit value".)

@P('{VAL_DESC} : a UTF-16 code unit')
class _:
    s_tb = T_code_unit_

@P('{VAL_DESC} : a code unit')
class _:
    s_tb = T_code_unit_

@P(r'{code_unit_lit} : \b 0x [0-9A-F]{4} \x20 \( [A-Z -]+ \)')
@P(r'{code_unit_lit} : the \x20 code \x20 unit \x20 0x [0-9A-F]{4} \x20 \( [A-Z -]+ \)')
class _:
    def s_expr(expr, env0, _):
        return (T_code_unit_, env0)

@P('{LITERAL} : {code_unit_lit}')
class _:
    s_tb = a_subset_of(T_code_unit_)
    s_expr = s_expr_pass_down

@P(r"{EX} : the code unit whose numeric value is {EX}")
class _:
    def s_expr(expr, env0, _):
        [ex] = expr.children
        env0.assert_expr_is_of_type(ex, T_MathNonNegativeInteger_)
        return (T_code_unit_, env0)

@P(r"{EX} : the code unit whose numeric value is determined by {PROD_REF} according to {h_emu_xref}")
class _:
    def s_expr(expr, env0, _):
        [nonterminal, emu_xref] = expr.children
        return (T_code_unit_, env0)

# ==============================================================================
# code point and/or code unit

@P(r"{NUM_COMPARAND} : the numeric value of {var}")
@P(r"{EX} : the numeric value of {EX}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        # polymorphic
        env1 = env0.ensure_expr_is_of_type(var, T_code_unit_ | T_code_point_)
        return (T_MathInteger_, env1)

@P(r'{CONDITION_1} : {var} occurs exactly once in {var}')
class _:
    def s_cond(cond, env0, asserting):
        [item_var, container_var] = cond.children
        (container_t, env1) = tc_expr(container_var, env0); assert env1 is env0
        # polymorphic
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

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 4 Overview

# ==============================================================================
#@ 4.2 Hosts and Implementations

@P(r"{CONDITION_1} : the host is a web browser")
class _:
    def s_cond(cond, env0, asserting):
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

    # grammar symbol

@P('{VAL_DESC} : a grammar symbol')
class _:
    s_tb = T_grammar_symbol_

    # -------------------
    # nonterminal symbols

@P(r'{nonterminal} : \| [A-Za-z][A-Za-z0-9]* \?? (\[ .+? \])? \|')
class _:
    def s_expr(expr, env0, _):
        nont_name = expr.source_text()[1:-1]
        # Note that |Foo| often denotes a Parse Node,
        # rather than a grammar symbol,
        # but we capture those cases before they can get to here.
        return (T_grammar_symbol_, env0)

@P(r"{EXPR} : the grammar symbol {nonterminal}")
class _:
    def s_expr(expr, env0, _):
        [nont] = expr.children
        return (T_grammar_symbol_, env0)

@P(r"{G_SYM} : {nonterminal}")
class _:
    def s_expr(expr, env0, _):
        return (T_grammar_symbol_, env0)

@P('{VAL_DESC} : {nonterminal}')
class _:
    def s_tb(val_desc, env):
        [nont] = val_desc.children
        return a_subset_of(T_grammar_symbol_)

@P('{VAL_DESC} : a nonterminal in one of the ECMAScript grammars')
class _:
    s_tb = a_subset_of(T_grammar_symbol_)

    # ----------------
    # terminal symbols

@P('{VAL_DESC} : {backticked_word}')
class _:
    s_tb = a_subset_of(T_grammar_symbol_)

@P(r"{G_SYM} : {TERMINAL}")
class _:
    def s_expr(expr, env0, _):
        return (T_grammar_symbol_, env0)

@P('{VAL_DESC} : the {nonterminal} {TERMINAL}')
class _:
    def s_tb(val_desc, env):
        [nont, term] = val_desc.children
        assert nont.source_text() == '|ReservedWord|'
        assert term.source_text() == "`super`"
        return a_subset_of(T_grammar_symbol_)

# ==============================================================================
#@ 5.1.4 The Syntactic Grammar

#> It defines a set of productions,
#> starting from two alternative goal symbols |Script| and |Module|, ...

@P(r"{CONDITION_1} : the goal symbol of the syntactic grammar is {nonterminal}")
class _:
    def s_cond(cond, env0, asserting):
        [nont] = cond.children
        return (env0, env0)

@P(r"{CONDITION_1} : the syntactic goal symbol is not {nonterminal}")
class _:
    def s_cond(cond, env0, asserting):
        [nont] = cond.children
        return (env0, env0)

#> When a parse is successful, it constructs a parse tree,
#> a rooted tree structure in which each node is a <dfn>Parse Node</dfn>.

@P('{VAL_DESC} : a Parse Node')
class _:
    s_tb = T_Parse_Node

@P('{LIST_ELEMENTS_DESCRIPTION} : Parse Nodes')
class _:
    s_tb = T_Parse_Node

#> Each Parse Node is an <em>instance</em> of a symbol in the grammar;
#> it represents a span of the source text that can be derived from that symbol.

@P('{VAL_DESC} : an instance of a nonterminal')
class _:
    s_tb = a_subset_of(T_Parse_Node)

@P('{VAL_DESC} : an instance of {var}')
class _:
    def s_tb(val_desc, env):
        [var] = val_desc.children
        env.assert_expr_is_of_type(var, T_grammar_symbol_)
        return a_subset_of(T_Parse_Node)

@P('{VAL_DESC} : an? {nonterminal}')
@P('{VAL_DESC} : an? {nonterminal} Parse Node')
class _:
    def s_tb(val_desc, env):
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

@P('{LIST_ELEMENTS_DESCRIPTION} : {nonterminal} Parse Nodes')
class _:
    def s_tb(led, env):
        [nonterminal] = led.children
        return ptn_type_for(nonterminal)

@P(r'{EXPR} : the source text that was recognized as {PROD_REF}')
class _:
    def s_expr(expr, env0, _):
        [nonterminal] = expr.children
        # XXX Should check whether nonterminal makes sense
        # with respect to the emu-grammar accompanying this alg/expr.
        return (T_Unicode_code_points_, env0)

@P(r"{EXPR} : the source text matched by {PROD_REF}")
class _:
    def s_expr(expr, env0, _):
        [nont] = expr.children
        return (T_Unicode_code_points_, env0) # XXX spec bug: needs to be T_String?

@P(r"{EX} : the code point matched by {PROD_REF}")
class _:
    def s_expr(expr, env0, _):
        [nont] = expr.children
        return (T_code_point_, env0)

@P(r"{EX} : the single code point matched by this production")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_code_point_, env0)

@P(r'{EX} : the number of code points in {PROD_REF}')
class _:
    def s_expr(expr, env0, _):
        [prod_ref] = expr.children
        env0.assert_expr_is_of_type(prod_ref, T_Parse_Node)
        return (T_MathNonNegativeInteger_, env0)

@P(r"{EX} : the number of code points in {PROD_REF}, excluding all occurrences of {nonterminal}")
class _:
    def s_expr(expr, env0, _):
        [prod_ref, nont] = expr.children
        return (T_MathNonNegativeInteger_, env0)

@P(r"{CONDITION_1} : any source text is matched by this production")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

    # 13.2.3.1
@P(r"{CONDITION_1} : {PROD_REF} is the token `false`")
@P(r"{CONDITION_1} : {PROD_REF} is the token `true`")
class _:
    def s_cond(cond, env0, asserting):
        [prod_ref] = cond.children
        assert prod_ref.source_text() == '|BooleanLiteral|'
        return (env0, env0)

#> When a Parse Node is an instance of a nonterminal,
#> it is also an instance of some production
#> that has that nonterminal as its left-hand side.

@P('{VAL_DESC} : an instance of a production in {h_emu_xref}')
class _:
    s_tb = a_subset_of(T_Parse_Node)

@P('{VAL_DESC} : an instance of the production {h_emu_grammar}')
class _:
    def s_tb(val_desc, env):
        [emu_grammar] = val_desc.children
        emu_grammar_text = emu_grammar.source_text()
        lhs = re.sub(r'<emu-grammar>(\w+) :.*', r'\1', emu_grammar_text)
        prodn_type = ptn_type_for(lhs)
        return a_subset_of(prodn_type)

@P(r"{EXPR} : an instance of the production {h_emu_grammar}")
class _:
    def s_expr(expr, env0, _):
        [emu_grammar] = expr.children
        assert emu_grammar.source_text() == '<emu-grammar>FormalParameters : [empty]</emu-grammar>'
        return (ptn_type_for('FormalParameters'), env0)

@P(r"{CONDITION_1} : {LOCAL_REF} is {h_emu_grammar}")
class _:
    def s_cond(cond, env0, asserting):
        [local_ref, h_emu_grammar] = cond.children
        env0.assert_expr_is_of_type(local_ref, T_Parse_Node)
        return (env0, env0)

@P(r"{CONDITION_1} : {LOCAL_REF} is {h_emu_grammar}, {h_emu_grammar}, {h_emu_grammar}, {h_emu_grammar}, or {h_emu_grammar}")
class _:
    def s_cond(cond, env0, asserting):
        [local_ref, *h_emu_grammar_] = cond.children
        env0.assert_expr_is_of_type(local_ref, T_Parse_Node)
        return (env0, env0)

@P(r'{CONDITION_1} : {PROD_REF} is `export` {nonterminal}')
class _:
    def s_cond(cond, env0, asserting):
        [prod_ref, nont] = cond.children
        return (env0, env0)

#> Moreover, it has zero or more <em>children</em>,
#> one for each symbol on the production's right-hand side:
#> each child is a Parse Node that is an instance of the corresponding symbol.

@P(r"{EACH_THING} : child node {DEFVAR} of this Parse Node")
class _:
    def s_nv(each_thing, env0):
        [loop_var] = each_thing.children
        env1 = env0.plus_new_entry(loop_var, T_Parse_Node)
        return env1

# (Each child of _P_ is 'nested' directly within _P_.)

@P(r"{CONDITION_1} : {LOCAL_REF} is not nested, directly or indirectly (but not crossing function or `static` initialization block boundaries), within an {nonterminal}")
class _:
    def s_cond(cond, env0, asserting):
        [local_ref, nont] = cond.children
        env0.assert_expr_is_of_type(local_ref, T_Parse_Node)
        return (env0, env0)

@P(r"{CONDITION_1} : {LOCAL_REF} is not nested, directly or indirectly (but not crossing function or `static` initialization block boundaries), within an {nonterminal} or a {nonterminal}")
class _:
    def s_cond(cond, env0, asserting):
        [local_ref, nonta, nontb] = cond.children
        env0.assert_expr_is_of_type(local_ref, T_Parse_Node)
        return (env0, env0)

# (_P_ 'contains' its children and their children, and so on)

@P(r"{CONDITION_1} : {var} contains a {nonterminal}")
@P(r"{CONDITION_1} : {var} contains an? {nonterminal} Parse Node")
@P(r"{CONDITION_1} : {var} does not contain an? {nonterminal} Parse Node")
@P(r"{CONDITION_1} : {var} does not contain two {nonterminal} Parse Nodes")
class _:
    def s_cond(cond, env0, asserting):
        [var, nont] = cond.children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        env0.assert_expr_is_of_type(nont, T_grammar_symbol_)
        return (env0, env0)

@P(r"{CONDITION_1} : {var} does not contain a rest parameter, any binding patterns, or any initializers. It may contain duplicate identifiers")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        return (env0, env0)

@P(r"{EACH_THING} : {nonterminal} {DEFVAR} that {var} contains")
class _:
    def s_nv(each_thing, env0):
        [nont, loop_var, root_var] = each_thing.children
        env0.assert_expr_is_of_type(root_var, T_Parse_Node)
        return env0.plus_new_entry(loop_var, ptn_type_for(nont))

@P(r"{EXPR} : the number of {h_emu_grammar} Parse Nodes contained within {var}")
class _:
    def s_expr(expr, env0, _):
        [emu_grammar, root_var] = expr.children
        env0.assert_expr_is_of_type(root_var, T_Parse_Node)
        return (T_MathNonNegativeInteger_, env0)

@P(r"{EXPR} : the number of {h_emu_grammar} Parse Nodes contained within {var} that either occur before {var} or contain {var}")
class _:
    def s_expr(expr, env0, _):
        [emu_grammar, root_var, x_var, x_var2] = expr.children
        env0.assert_expr_is_of_type(root_var, T_Parse_Node)
        env0.assert_expr_is_of_type(x_var, T_Parse_Node)
        assert x_var.source_text() == x_var2.source_text()
        return (T_MathNonNegativeInteger_, env0)

@P(r"{CONDITION_1} : {LOCAL_REF} contains two or more {nonterminal}s for which {NAMED_OPERATION_INVOCATION} is the same")
class _:
    def s_cond(cond, env0, asserting):
        [local_ref, nonta, noi] = cond.children
        env0.assert_expr_is_of_type(local_ref, T_Parse_Node)
        # XXX noi
        return (env0, env0)

# (You can ask about nodes that contain _P_)

@P(r"{PROD_REF} : the {nonterminal} containing {LOCAL_REF}")
class _:
    def s_expr(expr, env0, _):
        [nonta, local_ref] = expr.children
        return (T_Parse_Node, env0)

@P(r"{EXPR} : the {nonterminal}, {nonterminal}, or {nonterminal} that most closely contains {var}")
class _:
    def s_expr(expr, env0, _):
        [*nont_, var] = expr.children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        return (T_Parse_Node, env0)

@P(r"{CONDITION_1} : {var} is not contained within an? {nonterminal}, an? {nonterminal}, or an? {nonterminal}")
class _:
    def s_cond(cond, env0, asserting):
        [var, *nont_] = cond.children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        return (env0, env0)

@P(r"{CONDITION_1} : {PROD_REF} is contained within a {nonterminal} that is being parsed for JSON.parse (see step {h_emu_xref} of {h_emu_xref})")
@P(r"{CONDITION_1} : {PROD_REF} is contained within a {nonterminal} that is being evaluated for JSON.parse (see step {h_emu_xref} of {h_emu_xref})")
class _:
    def s_cond(cond, env0, asserting):
        [prod_ref, nont, step_xref, alg_xref] = cond.children
        env0.assert_expr_is_of_type(prod_ref, T_Parse_Node)
        return (env0, env0)

#> Parse Nodes are considered <dfn>the same Parse Node</dfn>
#> if and only if they represent the same span of source text,
#> are instances of the same grammar symbol,
#> and resulted from the same parser invocation.

@P(r"{CONDITION_1} : {EX} is the same Parse Node as {EX}")
class _:
    def s_cond(cond, env0, asserting):
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

@P(r"{EE_RULE} : {LOCAL_REF} must cover an? {nonterminal}.")
class _:
    def s_nv(anode, env0):
        [local_ref, nont] = anode.children
        env0.assert_expr_is_of_type(local_ref, T_Parse_Node)
        return None

@P(r"{EXPR} : the {nonterminal} that is covered by {LOCAL_REF}")
class _:
    def s_expr(expr, env0, _):
        [nonterminal, local_ref] = expr.children
        env0.assert_expr_is_of_type(local_ref, T_Parse_Node)
        return (ptn_type_for(nonterminal), env0)

# (this text would be matched by that nonterminal/production
# if it were source text in an appropriate context)

@P(r"{CONDITION_1} : {NAMED_OPERATION_INVOCATION} is not some Unicode code point matched by the {nonterminal} lexical grammar production")
class _:
    def s_cond(cond, env0, asserting):
        [noi, nont] = cond.children
        env0.assert_expr_is_of_type(noi, T_code_point_)
        return (env0, env0)

@P(r"{CONDITION_1} : {NAMED_OPERATION_INVOCATION} is not matched by the {nonterminal} lexical grammar production")
class _:
    def s_cond(cond, env0, asserting):
        [noi, nont] = cond.children
        env0.assert_expr_is_of_type(noi, T_code_point_)
        return (env0, env0)

@P(r"{CONDITION_1} : {NAMED_OPERATION_INVOCATION} is not the numeric value of some code point matched by the {nonterminal} lexical grammar production")
class _:
    def s_cond(cond, env0, asserting):
        [noi, nont] = cond.children
        env0.assert_expr_is_of_type(noi, T_MathInteger_)
        return (env0, env0)

# ==============================================================================
#@ 5.1.5.4 Grammatical Parameters

@P(r"{CONDITION_1} : {PROD_REF} has an? <sub>[{cap_word}]</sub> parameter")
class _:
    def s_cond(cond, env0, asserting):
        [prod_ref, cap_word] = cond.children
        return (env0, env0)

@P(r"{CONDITION_1} : the <sub>[Tagged]</sub> parameter was not set")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

# ==============================================================================
#@ 5.2 Algorithm Conventions

@P(r"{CONDITION_1} : control reaches here")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

# ------------------------------------------------------------------------------
#> The specification often uses a numbered list to specify steps in an algorithm.
#> Algorithm steps may be subdivided into sequential substeps.
#> Substeps are indented
#> and may themselves be further divided into indented substeps.

@P(r'{EMU_ALG_BODY} : {IND_COMMANDS}{nlai}')
class _:
    def s_nv(anode, env0):
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

@P(r'{COMMANDS} : {COMMANDS}{_NL_N} {COMMAND}')
class _:
    def s_nv(anode, env0):
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

@P(r'{IF_CLOSED} : If {CONDITION}, {SMALL_COMMAND}. Otherwise {SMALL_COMMAND}.')
@P(r'{IF_CLOSED} : If {CONDITION}, {SMALL_COMMAND}. Otherwise, {SMALL_COMMAND}.')
@P(r'{IF_CLOSED} : If {CONDITION}, {SMALL_COMMAND}; else {SMALL_COMMAND}.')
@P(r'{IF_CLOSED} : If {CONDITION}, {SMALL_COMMAND}; otherwise {SMALL_COMMAND}.')
@P(r'{IF_CLOSED} : If {CONDITION}, {SMALL_COMMAND}; otherwise, {SMALL_COMMAND}.')
class _:
    def s_nv(anode, env0):
        [cond, t_command, f_command] = anode.children
        (t_env, f_env) = tc_cond(cond, env0)
        t_benv = tc_nonvalue(t_command, t_env)
        f_benv = tc_nonvalue(f_command, f_env)
        return env_or(t_benv, f_benv)

@P(r'{IF_CLOSED} : If {CONDITION}, {SMALL_COMMAND}; else if {CONDITION}, {SMALL_COMMAND}; else {SMALL_COMMAND}.')
class _:
    def s_nv(anode, env0):
        [cond_a, command_a, cond_b, command_b, command_c] = anode.children
        (a_t_env, a_f_env) = tc_cond(cond_a, env0)
        a_benv = tc_nonvalue(command_a, a_t_env)
        (b_t_env, b_f_env) = tc_cond(cond_b, a_f_env)
        b_benv = tc_nonvalue(command_b, b_t_env)
        c_benv = tc_nonvalue(command_c, b_f_env)
        return envs_or([a_benv, b_benv, c_benv])

@P(r'{IF_OTHER} : {IF_OPEN}{IF_TAIL}')
class _:
    def s_nv(anode, env0):
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

                # TODO: These tests should apply to the initial `If` condition too:
                if t_env is None:
                    add_pass_error(
                        condition,
                        "STA says condition cannot be true, so SKIPPING analysis of consequent"
                    )
                    # Hopefully this is a transient situation,
                    # and {condition} can be true in a later pass.
                else:
                    benvs.append( tc_nonvalue(then_part, t_env) )

                if f_env is None:
                    add_pass_error(
                        condition,
                        "STA says condition cannot be false, so SKIPPING analysis of rest of If"
                    )
                    break

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

    # -------------------------------------------------

@P(r"{EXPR} : {EX} if {CONDITION}. Otherwise, it is {EXPR}")
class _:
    def s_expr(expr, env0, _):
        [exa, cond, exb] = expr.children
        (t_env, f_env) = tc_cond(cond, env0)
        (ta, enva) = tc_expr(exa, t_env)
        (tb, envb) = tc_expr(exb, f_env)
        return (ta | tb, env_or(enva, envb))

# ------------------------------------------------------------------------------
#> A step may specify the iterative application of its substeps.</p>

@P(r'{COMMAND} : Repeat,{IND_COMMANDS}')
class _:
    def s_nv(anode, env0):
        [commands] = anode.children

        def check_before_body(env):
            return (env, None)
            # The only way to leave a condition-less Repeat
            # is via a Return command,
            # so there can't be anything (except maybe a NOTE) after the loop.

        return tc_loop(env0, check_before_body, commands)

@P(r'{COMMAND} : Repeat, while {CONDITION},{IND_COMMANDS}')
@P(r"{COMMAND} : Repeat, until {CONDITION},{IND_COMMANDS}")
class _:
    def s_nv(anode, env0):
        [cond, commands] = anode.children

        def check_before_body(env):
            (t_env, f_env) = tc_cond(cond, env)
            p = str(anode.prod)
            if 'while' in p:
                # proceed to commands iff condition is True; exit iff it's False
                return (t_env, f_env)
            elif 'until' in p:
                # proceed to commands iff condition is False; exit iff it's True
                return (f_env, t_env)
            else:
                assert 0

        result = tc_loop(env0, check_before_body, commands)

        # hack!:
        if cond.source_text() == '_matchSucceeded_ is *false*': # in RegExpBuiltinExec
            # This case requires that variable _r_, introduced within the loop,
            # survive the loop.
            # (It doesn't have to survive from one iteration to the next,
            # just from the last iteration to after.)
            result = result.plus_new_entry('_r_', T_MatchState)

        return result

@P(r"{COMMAND} : While {CONDITION}, an implementation may perform the following steps:{IND_COMMANDS}")
class _:
    def s_nv(anode, env0):
        [cond, commands] = anode.children

        def check_before_body(env):
            (t_env, f_env) = tc_cond(cond, env)
            return (t_env, f_env)

        return tc_loop(env0, check_before_body, commands)

@P(r'{COMMAND} : For each {EACH_THING}, do{IND_COMMANDS}')
@P(r'{COMMAND} : For each {EACH_THING}, {SMALL_COMMAND}.')
class _:
    def s_nv(anode, env0):
        [each_thing, commands] = anode.children

        def check_before_body(env):
            env_for_commands  = tc_nonvalue(each_thing, env)
            return (env_for_commands, env)

        return tc_loop(env0, check_before_body, commands)

def tc_loop(preloop_env, check_before_body, commands):
    preloop_keys = preloop_env.vars.keys()

    traceme = False and ('_thisEnv_' in preloop_keys)

    global pass_errors
    mark = len(pass_errors)

    top_env = preloop_env
    for passi in range(1, 6):
        if traceme:
            print()
            print('--------------')
            print(passi)
            print()
            print("top_env:")
            pprint(top_env.vars)

        (stay_env, exit_env) = check_before_body(top_env)
        # "stay" means "stay in the loop", i.e. proceed to execute the commands

        if traceme:
            print()
            print("stay_env:")
            pprint(stay_env.vars)

        bottom_env = tc_nonvalue(commands, stay_env)

        if traceme:
            print()
            print("bottom_env:")
            pprint(bottom_env.vars)

        # At the bottom of the loop,
        # all the bindings introduced by the loop are wiped out.
        reduced_bottom_env = bottom_env.reduce(preloop_keys)

        # And then we merge that with the preloop_env.
        # E.g., consider
        #     1. Let _x_ be *undefined*.
        #     2. Repeat,
        #       a. refer to _x_
        #       b. Let _x_ be *"foo"*.
        #       c. refer to _x_.
        # On the first pass, _x_ will have type T_Undefined.
        # But then at 2b, its type is changes to T_String,
        # which then persists (because _x_ is defined before the loop).
        # So on the second pass, its type at 2a should be T_Undefined|T_String,
        # which means we have to combine the bottom-of-first-pass env with the preloop env.
        new_top_env = env_or(reduced_bottom_env, preloop_env)

        if new_top_env.equals(top_env):
            # No point going around again,
            # we have achieved a fixed-point.
            # (Accept the errors from the latest time through the loop.)
            assert 1 <= passi <= 2, passi
            if traceme: pdb.set_trace()
            return exit_env

        if traceme:
            print('DIFF!:')
            top_env.diff(new_top_env)

        # We're going around again,
        # so discard the errors from the latest time:
        del pass_errors[mark:]
        # and install the new top_env:
        top_env = new_top_env

    # failed to achieve a fixed-point in a reasonable number of attempts
    assert 0

@P(r"{EACH_THING} : {ITEM_NATURE} {DEFVAR} such that {CONDITION}")
@P(r"{EACH_THING} : {ITEM_NATURE} {DEFVAR} such that {CONDITION}, in ascending order")
@P(r"{EACH_THING} : {ITEM_NATURE} {DEFVAR} such that {CONDITION}, in descending order")
class _:
    def s_nv(each_thing, env0):
        [item_nature, loop_var, condition] = each_thing.children
        item_type = {
            "FinalizationRegistry": T_FinalizationRegistry_object_,
            "WeakMap"             : T_WeakMap_object_,
            "WeakRef"             : T_WeakRef_object_,
            "WeakSet"             : T_WeakSet_object_,
            "event"               : T_Shared_Data_Block_Event,
            "integer"             : T_MathInteger_,
        }[item_nature.prod.rhs_s]
        env1 = env0.plus_new_entry(loop_var, item_type)
        (tenv, fenv) = tc_cond(condition, env1)
        return tenv

@P("{EACH_THING} : {ITEM_NATURE} {DEFVAR} of {EX}")
class _:
    def s_nv(each_thing, env0):
        [item_nature, loop_var, collection_expr] = each_thing.children

        # There's two approaches:
        # outside-in: Get the type of {EX}, then ensure that {ITEM_NATURE} is consistent.
        # inside-out: Convert {ITEM_NATURE} to a type, then ensure {EX} is consistent.
        # ("ensure it's consistent" = if it isn't consistent, complain and force it to be consistent)
        #
        # Most of the time, it doesn't matter which approach you use.
        #
        # One typical source of inconsistency is when {EX}'s static type isn't precise enough
        # (e.g., it's just "a List"), in which case inside-out works better.
        #
        # OTOH, when {ITEM_NATURE} is `Record { {DSBN} ... }`,
        # that doesn't convert to a precise type,
        # so you need to go outside-in to get the precise type of the loop-variable.

        if item_nature.prod.rhs_s.startswith('Record {'):
            # outside-in
            (collection_type, env1) = tc_expr(collection_expr, env0)
            assert isinstance(collection_type, ListType)
            item_type = collection_type.element_type
            assert item_type.is_a_subtype_of_or_equal_to(T_Record)
            assert isinstance(item_type, RecordType)
            assert item_type.schema_name == ''
            fields_dict = dict(item_type.fields_info)

            assert len(fields_dict) == len(item_nature.children)
            for dsbn in item_nature.children:
                assert dsbn.source_text() in fields_dict
                
            return env1.plus_new_entry(loop_var, item_type)

        # -----
        # Otherwise, inside-out...

        if item_nature.prod.rhs_s == "code point":
            item_type = T_code_point_
            collection_type = T_Unicode_code_points_

        elif item_nature.prod.rhs_s == r"event":
            item_type = T_Event
            collection_type = T_Set | ListType(T_Event)

        elif item_nature.prod.rhs_s == r"ReadSharedMemory or ReadModifyWriteSharedMemory event":
            item_type = T_ReadSharedMemory_Event | T_ReadModifyWriteSharedMemory_Event
            collection_type = T_Set

        elif item_nature.prod.rhs_s == "{nonterminal}":
            [nont] = item_nature.children
            item_type = ptn_type_for(nont)
            collection_type = ListType(T_Parse_Node)

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

@P(r"{CONDITION_1} : The following loop will terminate")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

# ------------------------------------------------------------------------------
#> A step that begins with “<dfn>Assert</dfn>:”
#> asserts an invariant condition of its algorithm.

@P(r'{COMMAND} : Assert: {CONDITION}.')
class _:
    def s_nv(anode, env0):
        [condition] = anode.children
        (t_env, f_env) = tc_cond(condition, env0, asserting=True)
        # throw away f_env
        return t_env

@P(r"{COMMAND} : Assert: If {CONDITION}, then {CONDITION}.")
@P(r"{COMMAND} : Assert: If {CONDITION}, {CONDITION}.")
class _:
    def s_nv(anode, env0):
        [cond1, cond2] = anode.children
        (t1_env, f1_env) = tc_cond(cond1, env0)
        (t2_env, f2_env) = tc_cond(cond2, t1_env, asserting=True)
        return env_or(f1_env, t2_env)

@P(r"{COMMAND} : Assert: {CONDITION_1} if and only if {CONDITION_1}.")
class _:
    def s_nv(anode, env0):
        [cond1, cond2] = anode.children
        (t1_env, f1_env) = tc_cond(cond1, env0)
        (t2_env, f2_env) = tc_cond(cond2, env0)
        return env_or(
            env_and(t1_env, t2_env),
            env_and(f1_env, f2_env)
        )

@P(r"{COMMAND} : Assert: {CONDITION_1} if {CONDITION_1}; otherwise, {CONDITION_1}.")
class _:
    def s_nv(anode, env0):
        [cond_t, cond_x, cond_f] = anode.children
        (xt_env, xf_env) = tc_cond(cond_x, env0)
        (tt_env, tf_env) = tc_cond(cond_t, xt_env, asserting=True)
        (ft_env, ff_env) = tc_cond(cond_f, xf_env, asserting=True)
        return env_or(tt_env, ft_env)

@P(r"{COMMAND} : Assert: {CONDITION_1}, since {CONDITION_1}.")
class _:
    def s_nv(anode, env0):
        [conda, condb] = anode.children
        (ta_env, fa_env) = tc_cond(conda, env0, asserting=True)
        (tb_env, fb_env) = tc_cond(condb, env0, asserting=True)
        return env_and(ta_env, tb_env)

# ------------------------------------------------------------------------------
#> Algorithm steps may declare named aliases for any value
#> using the form “Let _x_ be _someValue_”.

@P(r'{var} : \b _ [A-Za-z][A-Za-z0-9]* _ \b')
class _:
    def s_expr(expr, env0, _):
        [var_name] = expr.children
        return (env0.vars[var_name], env0)

    # Let {DEFVAR} be ...

@P(r"{COMMAND} : Let {DEFVAR} be {EXPR}. (It may be evaluated repeatedly.)")
@P(r"{COMMAND} : Let {DEFVAR} be {EXPR}.")
@P(r"{COMMAND} : Let {DEFVAR} be {MULTILINE_EXPR}")
@P(r"{SMALL_COMMAND} : let {DEFVAR} be {EXPR}")
@P(r"{SMALL_COMMAND} : let {DEFVAR} be {EXPR}, indicating that an ordinary object should be created as the global object")
@P(r"{SMALL_COMMAND} : let {DEFVAR} be {EXPR}, indicating that {var}'s global `this` binding should be the global object")
class _:
    def s_nv(anode, env0):
        [var, expr] = anode.children[0:2]
        var_name = var.source_text()

        (expr_t, env1) = tc_expr(expr, env0)
        return env1.plus_new_entry(var, expr_t)

@P(r"{COMMAND} : Let {DEFVAR} be {EXPR}. (However, if {var} = 10 and {var} contains more than 20 significant digits, every significant digit after the 20th may be replaced by a 0 digit, at the option of the implementation; and if {var} is not one of 2, 4, 8, 10, 16, or 32, then {var} may be an implementation-approximated integer representing the integer value denoted by {var} in radix-{var} notation.)")
class _:
    def s_nv(anode, env0):
        [let_var, expr, rvar, zvar, rvar2, let_var2, zvar2, rvar3] = anode.children
        assert same_source_text(let_var, let_var2)
        assert same_source_text(rvar, rvar2)
        assert same_source_text(rvar, rvar3)
        assert same_source_text(zvar, zvar2)
        (t, env1) = tc_expr(expr, env0)
        return env1.plus_new_entry(let_var, t)

@P(r"{COMMAND} : Let {DEFVAR} be an integer for which {NUM_EXPR} is as close to zero as possible. If there are two such {var}, pick the larger {var}.")
class _:
    def s_nv(anode, env0):
        [let_var, num_expr, var2, var3] = anode.children
        assert same_source_text(var2, let_var)
        assert same_source_text(var3, let_var)
        new_env = env0.plus_new_entry(let_var, T_MathInteger_)
        new_env.assert_expr_is_of_type(num_expr, T_MathReal_)
        return new_env

    # Let {DEFVAR} and {DEFVAR} ... be ...

@P(r"{COMMAND} : Let {DEFVAR} and {DEFVAR} be the indirection values provided when this binding for {var} was created.")
class _:
    def s_nv(anode, env0):
        [m_var, n2_var, n_var] = anode.children
        env0.assert_expr_is_of_type(n_var, T_String)
        return env0.plus_new_entry(m_var, T_Module_Record).plus_new_entry(n2_var, T_String)

@P(r"{COMMAND} : Let {DEFVAR} and {DEFVAR} be integers such that {CONDITION} and for which {NUM_EXPR} is as close to zero as possible. If there are two such sets of {var} and {var}, pick the {var} and {var} for which {PRODUCT} is larger.")
class _:
    def s_nv(anode, env0):
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

@P(r"{COMMAND} : Let {DEFVAR}, {DEFVAR}, and {DEFVAR} be integers such that {CONDITION}. If there are multiple possibilities for {var}, choose the value of {var} for which {EX} is closest in value to {EX}. If there are two such possible values of {var}, choose the one that is even. Note that {var} is the number of digits in the representation of {var} using radix {var} and that {var} is not divisible by {var}.")
@P(r"{COMMAND} : Let {DEFVAR}, {DEFVAR}, and {DEFVAR} be integers such that {CONDITION}. Note that the decimal representation of {var} has {SUM} digits, {var} is not divisible by 10, and the least significant digit of {var} is not necessarily uniquely determined by these criteria.")
@P(r"{COMMAND} : Let {DEFVAR}, {DEFVAR}, and {DEFVAR} be integers such that {CONDITION}. Note that {var} is the number of digits in the representation of {var} using radix {var}, that {var} is not divisible by {var}, and that the least significant digit of {var} is not necessarily uniquely determined by these criteria.")
class _:
    def s_nv(anode, env0):
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

@P(r"{EXPR} : a copy of {EX}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        (t, env1) = tc_expr(var, env0); assert env1 is env0
        return (t, env1)

#> Once declared, an alias may be referenced in any subsequent steps
#> and must not be referenced from steps prior to the alias's declaration.

@P(r'{SETTABLE} : {var}')
class _:
    def s_expr(expr, env0, _):
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

@P(r'{EXPR} : {EX}, where {DEFVAR} is {EX}')
class _:
    def s_expr(expr, env0, _):
        [exa, var, exb] = expr.children
        (exb_type, env1) = tc_expr(exb, env0); assert env1 is env0
        env2 = env1.plus_new_entry(var, exb_type)
        (exa_type, env3) = tc_expr(exa, env2)
        return (exa_type, env3)

@P(r'{EXPR} : {EX}, where {DEFVAR} is {EX} and {DEFVAR} is {EX}')
@P(r'{EXPR} : {EX}, where {DEFVAR} is {EX}, and {DEFVAR} is {EX}')
class _:
    def s_expr(expr, env0, _):
        [ex3, var2, ex2, var1, ex1] = expr.children

        (ex1_type, ex1_env) = tc_expr(ex1, env0); assert ex1_env is env0
        env1 = ex1_env.plus_new_entry(var1, ex1_type)

        (ex2_type, ex2_env) = tc_expr(ex2, env1); assert ex2_env is env1
        env2 = ex2_env.plus_new_entry(var2, ex2_type)

        (ex3_type, ex3_env) = tc_expr(ex3, env2); assert ex3_env is env2
        return (ex3_type, ex3_env)

# ------------------------------------------------------------------------------
#> Aliases may be modified using the form “Set _x_ to _someOtherValue_”.</p>

@P(r'{COMMAND} : Set {SETTABLE} to {EXPR}.')
@P(r'{COMMAND} : Set {SETTABLE} to {MULTILINE_EXPR}')
@P(r'{SMALL_COMMAND} : set {SETTABLE} to {EXPR}')
class _:
    def s_nv(anode, env0):
        [settable, expr] = anode.children
        return env0.set_A_to_B(settable, expr)

@P(r'{COMMAND} : Set {DOTTING} as described in {h_emu_xref}.')
@P(r'{COMMAND} : Set {DOTTING} as specified in {h_emu_xref}.')
@P(r'{COMMAND} : Set {DOTTING} to the definition specified in {h_emu_xref}.')
class _:
    def s_nv(anode, env0):
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
        if curr_base_t == implied_base_t:
            return env1
        elif curr_base_t == T_Object:
            return env1.with_expr_type_narrowed(base_var, implied_base_t)
        else:
            add_pass_error_re_wrong_type(base_var, curr_base_t, implied_base_t)
            return env1.with_expr_type_replaced(base_var, implied_base_t)

# ------------------------------------------------------------------------------
# (This section is where "Return" steps should be mentioned?)

@P(r"{COMMAND} : Return {EXPR}.")
@P(r"{COMMAND} : Return {EXPR}. This may be of type Reference.")
@P(r"{COMMAND} : Return {MULTILINE_EXPR}")
@P(r"{SMALL_COMMAND} : return {EXPR}")
class _:
    def s_nv(anode, env0):
        [expr] = anode.children
        (t1, env1) = tc_expr(expr, env0)
        # assert env1 is env0
        if False and trace_this_op:
            print("Return command's expr has type", t1)
        proc_add_return(env1, t1, anode)
        return None

# ------------------------------------------------------------------------------
# (This section is where "Note" steps should be mentioned?)

@P(r'{COMMAND} : {note}')
class _:
    def s_nv(anode, env0):
        return env0

# ------------------------------------------------------------------------------
# (This section is where conditions should be mentioned?)

@P(r'{CONDITION} : {CONDITION_1}')
@P(r'{CONDITION_1} : {TYPE_TEST}')
@P(r'{CONDITION_1} : {NUM_COMPARISON}')
@P(r'{CONDITION_1} : {NUM_COMPARISON} (ignoring potential non-monotonicity of time values)')
class _:
    def s_cond(cond, env0, asserting):
        [child] = cond.children
        return tc_cond(child, env0, asserting)

@P(r"{CONDITION} : {CONDITION_1} or {CONDITION_1}")
@P(r"{CONDITION} : {CONDITION_1}, or if {CONDITION_1}")
@P(r"{CONDITION} : {CONDITION_1}, {CONDITION_1}, or {CONDITION_1}")
@P(r"{CONDITION} : {CONDITION_1}, {CONDITION_1}, {CONDITION_1}, or {CONDITION_1}")
class _:
    def s_cond(cond, env0, asserting):
        logical = ('or', cond.children)
        return tc_logical(logical, env0, asserting)

@P(r'{CONDITION} : {CONDITION_1} and {CONDITION_1}')
@P(r"{CONDITION} : {CONDITION_1}, {CONDITION_1}, and {CONDITION_1}")
@P(r'{CONDITION} : {CONDITION_1}, {CONDITION_1}, {CONDITION_1}, and {CONDITION_1}')
class _:
    def s_cond(cond, env0, asserting):
        logical = ('and', cond.children)
        return tc_logical(logical, env0, asserting)

@P(r"{CONDITION} : {CONDITION_1}, or if {CONDITION_1} and {CONDITION_1}")
class _:
    def s_cond(cond, env0, asserting):
        [conda, condb, condc] = cond.children
        logical = (
            'or',
            [
                conda,
                ('and', [condb, condc])
            ]
        )
        return tc_logical(logical, env0, asserting)

@P(r"{CONDITION} : {CONDITION_1} or {CONDITION_1} <ins>and {CONDITION_1}</ins>")
class _:
    def s_cond(cond, env0, asserting):
        [a, b, c] = cond.children
        logical = (
            'and',
            [
                ('or', [a, b]),
                c
            ]
        )
        return tc_logical(logical, env0, asserting)

@P(r"{CONDITION} : {CONDITION_1} and {CONDITION_1}, or if {CONDITION_1} and {CONDITION_1}")
@P(r"{CONDITION} : {CONDITION_1} and {CONDITION_1}, or {CONDITION_1} and {CONDITION_1}")
class _:
    def s_cond(cond, env0, asserting):
        [a, b, c, d] = cond.children
        logical = (
            'or',
            [
                ('and', [a, b]),
                ('and', [c, d]),
            ]
        )
        return tc_logical(logical, env0, asserting)

@P(r"{CONDITION} : ({NUM_COMPARISON} or {NUM_COMPARISON}) and ({NUM_COMPARISON} or {NUM_COMPARISON})")
class _:
    def s_cond(cond, env0, asserting):
        [a, b, c, d] = cond.children
        logical = (
            'and',
            [
                ('or', [a, b]),
                ('or', [c, d]),
            ]
        )
        return tc_logical(logical, env0, asserting)

@P(r"{CONDITION} : {CONDITION_1} unless {CONDITION_1}")
@P(r"{CONDITION} : {CONDITION_1}, unless {CONDITION_1}")
class _:
    def s_cond(cond, env0, asserting):
        [conda, condb] = cond.children
        tc_cond(conda, env0)
        tc_cond(condb, env0)
        return (env0, env0)

@P(r"{CONDITION} : {CONDITION_1} unless {CONDITION_1} and {CONDITION_1}")
class _:
    def s_cond(cond, env0, asserting):
        [conda, condb, condc] = cond.children
        tc_cond(conda, env0)
        tc_cond(condb, env0)
        tc_cond(condc, env0)
        return (env0, env0)

# ==============================================================================
#@ 5.2.1 Abstract Operations

@P(r"{COMMAND} : Perform {PP_NAMED_OPERATION_INVOCATION}.")
@P(r"{COMMAND} : Perform {PP_NAMED_OPERATION_INVOCATION}. {note}")
@P(r"{SMALL_COMMAND} : perform {PP_NAMED_OPERATION_INVOCATION}")
class _:
    def s_nv(anode, env0):
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

@P(r"{PP_NAMED_OPERATION_INVOCATION} : {NAMED_OPERATION_INVOCATION}")
class _:
    def s_expr(expr, env0, expr_value_will_be_discarded):
        [noi] = expr.children
        (noi_t, env1) = tc_expr(noi, env0, expr_value_will_be_discarded)
        if noi_t == T_TBD:
            # Don't do the comparison to Normal,
            # because that loses the TBD-ness,
            # which is used as a sentinel all over.
            return (noi_t, env1)
        else:
            # (normal_part_of_type, abrupt_part_of_type) = noi_t.split_by(T_normal_completion)
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

@P(r"{NAMED_OPERATION_INVOCATION} : {h_emu_meta_start}{NAMED_OPERATION_INVOCATION}{h_emu_meta_end}")
class _:
    def s_expr(expr, env0, _):
        [_, noi, _] = expr.children
        return tc_expr(noi, env0)

@P(r"{NAMED_OPERATION_INVOCATION} : {PREFIX_PAREN} (see {h_emu_xref})")
class _:
    def s_expr(expr, env0, _):
        [pp, _] = expr.children
        return tc_expr(pp, env0)

#> Abstract operations are typically referenced using a functional application style
#> such as OperationName(_arg1_, _arg2_).

@P(r'{PREFIX_PAREN} : {OPN_BEFORE_PAREN}({EXLIST_OPT})')
class _:
    def s_expr(expr, env0, _):
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

            base_schema_name = {
                'op: discriminated by type: env rec'   : 'Environment Record',
                'op: discriminated by type: module rec': 'Module Record'
            }[callee_op.species]

            base_record_schema = spec.RecordSchema_for_name_[base_schema_name]

            def each_record_schema_that_declares_op(rs):
                if callee_op_name in rs.addl_method_decls:
                    yield rs
                    # And don't go any deeper.
                    # (In practice, going deeper wouldn't yield any more results,
                    # because there's no point re-declaring a method at a deeper level.
                    # So this is just an optimization.)
                else:
                    # callee_op_name is not declared for {rs},
                    # but it might be declared for one or more sub-schemas.
                    for child_rs in rs.sub_schemas:
                        yield from each_record_schema_that_declares_op(child_rs)

            forp_types = [
                HierType(rs.tc_schema_name)
                for rs in each_record_schema_that_declares_op(base_record_schema)
            ]
            assert forp_types
            # TODO: This could be pre-computed, put in callee_op.

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
                return_type = NormalCompletionType(arg_type)
                return (return_type, env0)
                # don't call tc_args etc

            elif callee_op_name == 'ThrowCompletion':
                assert len(args) == 1
                [arg] = args
                (arg_type, arg_env) = tc_expr(arg, env0); assert arg_env is env0
                if arg_type == T_TBD: arg_type = T_Normal
                assert arg_type.is_a_subtype_of_or_equal_to(T_Normal)
                return_type = ThrowCompletionType(arg_type)
                return (return_type, env0)

            elif callee_op_name == 'Completion':
                assert len(args) == 1
                [arg] = args
                (return_type, env1) = env0.ensure_expr_is_of_type_(arg, T_Completion_Record)
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

                if callee_op_name in ['IteratorClose', 'AsyncIteratorClose']:
                    assert return_type == T_Completion_Record
                    # but we can be more specific.
                    # And we need to be more specific to avoid some complaints.
                    #
                    # E.g., Promise.all has roughly:
                    #     8. If _result_ is an abrupt completion, then
                    #       a. ... set _result_ to Completion(IteratorClose(_, _result_)).
                    #       b. IfAbruptRejectPromise(_result_, _).
                    #     9. Return ? _result_.
                    #
                    # If IteratorClose has a return type of T_Completion_Record,
                    # then after 8.a, _result_ can be a normal or abrupt completion,
                    # and a normal completion will survive 8.b's call to IfAbruptRejectPromise,
                    # and after 8.b, _result_ will be the [[Value]] of that normal completion,
                    # which will cause 9's `?` to complain that it's being given a non-completion.
                    #
                    # Instead, before 8.a, we know that _result_ is abrupt,
                    # so using a smarter return type for IteratorClose,
                    # we know that _result_ must be abrupt too,
                    # so nothing will survive the call to IfAbruptRejectPromise,
                    # and 9 won't get a non-completion.
                    # (In fact, it will *only* get a normal completion,
                    # so the '?' should actually be '!', but that's a separate problem.)
                    #
                    assert len(args) == 2
                    [_, cr_arg] = args
                    (cr_arg_type, _) = tc_expr(cr_arg, env0)
                    return_type = T_throw_completion | cr_arg_type

                elif callee_op_name == 'CreateListFromArrayLike' and len(args) == 2:
                    # The second arg is a list of ES language type names
                    # that constrains the return type.
                    assert return_type == NormalCompletionType(ListType(T_Tangible_)) | T_throw_completion
                    types_arg = args[1]
                    assert types_arg.source_text() == '« String, Symbol »'
                    return_type = NormalCompletionType(ListType(T_String | T_Symbol)) | T_throw_completion

                elif callee_op_name == 'ToIntegerOrInfinity':
                    assert return_type == NormalCompletionType(T_MathInteger_ | T_MathPosInfinity_ | T_MathNegInfinity_) | T_throw_completion
                    # but we can be more precise in some cases

                    assert len(args) == 1
                    [arg] = args
                    (arg_type, env1) = tc_expr(arg, env0); assert env1 is env0

                    return_type = T_0
                    for memtype in arg_type.set_of_types():
                        if memtype in [T_Tangible_, T_Object]:
                            return_type |= NormalCompletionType(T_MathInteger_ | T_MathPosInfinity_ | T_MathNegInfinity_) | T_throw_completion
                        elif memtype in [T_Number, T_String]:
                            return_type |= NormalCompletionType(T_MathInteger_ | T_MathPosInfinity_ | T_MathNegInfinity_)
                        elif memtype in [T_Boolean, T_Null, T_NaN_Number_, T_FiniteNumber_]:
                            return_type |= NormalCompletionType(T_MathInteger_)
                        elif memtype == T_NegInfinityNumber_:
                            return_type |= NormalCompletionType(T_MathNegInfinity_)
                        elif memtype == T_PosInfinityNumber_:
                            return_type |= NormalCompletionType(T_MathPosInfinity_)
                        elif memtype in [T_Symbol, T_BigInt]:
                            return_type |= T_throw_completion
                        elif memtype == T_not_passed:
                            pass
                        else:
                            assert 0, memtype

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

@P(r"{PROD_REF} : the {nonterminal} of {LOCAL_REF}")
class _:
    def s_expr(expr, env0, _):
        [nonterminal, var] = expr.children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        # XXX could check that t is a nonterminal that actually has a child of that type
        # but that requires having the whole grammar handy
        return (ptn_type_for(nonterminal), env0)

@P(r'{PROD_REF} : this {nonterminal}')
class _:
    def s_expr(expr, env0, _):
        [nonterminal] = expr.children
        # XXX check
        return (ptn_type_for(nonterminal), env0)

@P(r'{PROD_REF} : {nonterminal}')
class _:
    def s_expr(expr, env0, _):
        [nonterminal] = expr.children
        return (ptn_type_for(nonterminal), env0)

@P(r"{PROD_REF} : {nonterminal} {var}")
class _:
    def s_expr(expr, env0, _):
        [nonterminal, var] = expr.children
        t = ptn_type_for(nonterminal)
        env0.assert_expr_is_of_type(var, t)
        return (t, env0)

@P(r'{PROD_REF} : the {ORDINAL} {nonterminal}')
class _:
    def s_expr(expr, env0, _):
        [ordinal, nonterminal] = expr.children
        # XXX should check that the 'current' production has such.
        return (ptn_type_for(nonterminal), env0)

@P(r'{PROD_REF} : the {nonterminal}')
class _:
    def s_expr(expr, env0, _):
        nonterminal = expr.children[-1]
        return (ptn_type_for(nonterminal), env0)

@P(r"{PROD_REF} : that {nonterminal}")
class _:
    def s_expr(expr, env0, _):
        [nont] = expr.children
        return (ptn_type_for(nont), env0)

@P(r"{PROD_REF} : this phrase")
@P(r"{PROD_REF} : this production")
class _:
    def s_expr(expr, env0, _):
        return (T_Parse_Node, env0)

@P(r"{PROD_REF} : the derived {nonterminal}")
class _:
    def s_expr(expr, env0, _):
        [nont] = expr.children
        return (T_Parse_Node, env0)

@P('{VAL_DESC} : the {nonterminal} of an? {nonterminal}')
class _:
    def s_tb(val_desc, env):
        [nont1, nont2] = val_desc.children
        return a_subset_of(ptn_type_for(nont1))

@P(r'{CONDITION_1} : {LOCAL_REF} is present')
@P(r'{CONDITION_1} : {LOCAL_REF} is not present')
class _:
    def s_cond(cond, env0, asserting):
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

@P(r"{NAMED_OPERATION_INVOCATION} : the {cap_word} of {LOCAL_REF}")
@P(r"{NAMED_OPERATION_INVOCATION} : the {cap_word} of {LOCAL_REF} (see {h_emu_xref})")
@P(r"{NAMED_OPERATION_INVOCATION} : the {cap_word} of {LOCAL_REF} as defined in {h_emu_xref}")
@P(r"{NAMED_OPERATION_INVOCATION} : {cap_word} of {LOCAL_REF}")
@P(r"{NAMED_OPERATION_INVOCATION} : the result of performing {cap_word} on {EX}")
class _:
    def s_expr(expr, env0, _):
        [callee, local_ref] = expr.children[0:2]
        callee_op_name = callee.source_text()
        if callee_op_name in ['UTF16EncodeCodePoint', 'UTF16SurrogatePairToCodePoint']:
            # An abstract operation that uses SDO-style invocation.
            return tc_ao_invocation(callee_op_name, [local_ref], expr, env0)
        else:
            return tc_sdo_invocation(callee_op_name, local_ref, [], expr, env0)

@P(r"{NAMED_OPERATION_INVOCATION} : the {cap_word} of {LOCAL_REF} {WITH_ARGS}")
@P(r"{NAMED_OPERATION_INVOCATION} : {cap_word} of {LOCAL_REF} {WITH_ARGS}")
class _:
    def s_expr(expr, env0, _):
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

@P(r"{COMMAND} : Throw a {ERROR_TYPE} exception.")
@P(r"{SMALL_COMMAND} : throw a {ERROR_TYPE} exception because the structure is cyclical")
@P(r'{SMALL_COMMAND} : throw a {ERROR_TYPE} exception')
class _:
    def s_nv(anode, env0):
        [error_type] = anode.children
        proc_add_return(env0, ThrowCompletionType(type_for_ERROR_TYPE(error_type)), anode)
        return None

# ==============================================================================
#@ 5.2.3.3 ReturnIfAbrupt

@P(r"{COMMAND} : ReturnIfAbrupt({EX}).")
class _:
    def s_nv(anode, env0):
        [ex] = anode.children
        (_, env1) = handle_completion_record_shorthand('ReturnIfAbrupt', ex, env0)
        return env1

# ==============================================================================
#@ 5.2.3.4 ReturnIfAbrupt Shorthands

@P(r'{PP_NAMED_OPERATION_INVOCATION} : ? {NAMED_OPERATION_INVOCATION}')
@P(r"{EX} : ? {DOTTING}")
@P(r"{EX} : ? {var}")
class _:
    def s_expr(expr, env0, _):
        [operand] = expr.children
        return handle_completion_record_shorthand('?', operand, env0)

@P(r'{PP_NAMED_OPERATION_INVOCATION} : ! {NAMED_OPERATION_INVOCATION}')
class _:
    def s_expr(expr, env0, _):
        [noi] = expr.children
        return handle_completion_record_shorthand('!', noi, env0)

# --------------------------------------

def handle_completion_record_shorthand(operator, operand, env0):
    operand_text = operand.source_text()
    (operand_t, env1) = tc_expr(operand, env0)

    if operand_t == T_TBD:
        # No point trying to analyze operand_t.
        return (T_TBD, env1)

    (cr_part_of_type, noncr_part_of_type) = operand_t.split_by(T_Completion_Record)
    if cr_part_of_type == T_0:
        add_pass_error(
            operand,
            f"The ST of the operand is {operand_t}\n    of which no part is a completion record.\n    Maybe the `{operator}` should be removed."
        )
        return (noncr_part_of_type, env1)

    elif noncr_part_of_type != T_0:
        add_pass_error(
            operand,
            f"The ST of the operand is {operand_t}\n    which includes {noncr_part_of_type}\n    which is not a completion record, and which is omitted from further analysis."
        )

    (abrupt_part_of_type, normal_part_of_type) = cr_part_of_type.split_by(T_abrupt_completion)

    if operator == '!':
        # Dynamically, the value of the operand should always be a normal completion.
        # So you might think we'd complain if its static type includes an abrupt completion.
        if False and abrupt_part_of_type != T_0:
            add_pass_error(
                operand,
                f"The ST of `{operand_text}` is {cr_part_of_type}\n    i.e. can be abrupt completion, so maybe change '!' to '?'"
            )
        # The thing is, in most of the spots where '!' is used,
        # it isn't superficially obvious that the value of the operand is always a normal completion,
        # so it's actually pretty likely that STA will infer that the operand might be abrupt.
        # Enabling the above message would result in over 500 complaints,
        # possibly all of which might be false positives.

    else:
        # The operand's value should be sometimes normal, sometimes abrupt.
        # Complain if STA infers that it can't be abrupt.
        if abrupt_part_of_type == T_0:
            add_pass_error(
                operand,
                f"The ST of `{operand_text}` is {cr_part_of_type}\n    i.e. no abrupt completion, so maybe change `{operator}` to `!`"
            )

    # Regardless of the operator,
    # there should always be the possibility
    # that the operand's value is a normal completion.
    # So complain if STA infers that the operand can't be a normal completion.
    if normal_part_of_type == T_0:
        if operator == '?':
            conclusion = "so using '?' is a bit odd,\n    and will result in warnings that the '?' expr has an empty type"
        else:
            assert 0
        add_pass_error(
            operand,
            f"The ST of `{operand_text}` is {cr_part_of_type}\n    i.e. no normal completion, {conclusion}"
        )

    assert normal_part_of_type.is_a_subtype_of_or_equal_to(T_normal_completion)
    result_type = s_dot_field(normal_part_of_type, '[[Value]]')

    if operator == '!':
        return (result_type, env1)

    else:
        proc_add_return(env1, abrupt_part_of_type, operand)

        if operand.is_a('{var}'):
            env2 = env1.with_expr_type_replaced(operand, result_type)

        elif str(operand.prod) == '{NAMED_OPERATION_INVOCATION} : {PREFIX_PAREN}':
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

            else:
                env2 = env1

        else:
            env2 = env1

        return (result_type, env2)

# ==============================================================================
#@ 5.2.3.5 Implicit Normal Completion

# ==============================================================================
#@ 5.2.4 Static Semantics

#> A special kind of static semantic rule is an Early Error Rule.

@P(r"{EE_RULE} : It is a Syntax Error if {CONDITION}.")
@P(r"{EE_RULE} : It is an early Syntax Error if {CONDITION}.")
class _:
    def s_nv(anode, env0):
        [cond] = anode.children
        tc_cond(cond, env0, False)
        return None

@P(r"{EE_RULE} : <p>{_indent_}{nlai}It is a Syntax Error if {LOCAL_REF} is<br>{nlai}{h_emu_grammar}<br>{nlai}and {LOCAL_REF} ultimately derives a phrase that, if used in place of {LOCAL_REF}, would produce a Syntax Error according to these rules. This rule is recursively applied.{_outdent_}{nlai}</p>")
class _:
    def s_nv(anode, env0):
        [local_ref1, h_emu_grammar, local_ref2, local_ref3] = anode.children
        env0.assert_expr_is_of_type(local_ref1, T_Parse_Node)
        env0.assert_expr_is_of_type(local_ref2, T_Parse_Node)
        env0.assert_expr_is_of_type(local_ref3, T_Parse_Node)
        return None

@P(r"{EE_RULE} : If {CONDITION}, the Early Error rules for {h_emu_grammar} are applied.")
class _:
    def s_nv(anode, env0):
        [cond, h_emu_grammar] = anode.children
        tc_cond(cond, env0, False)
        return None

@P(r"{EE_RULE} : If {CONDITION}, it is a Syntax Error if {CONDITION}.")
class _:
    def s_nv(anode, env0):
        [conda, condb] = anode.children
        (tenv, fenv) = tc_cond(conda, env0, False)
        tc_cond(condb, tenv, False)
        return None

@P(r"{EE_RULE} : <p>It is a Syntax Error if {CONDITION_1} and the following algorithm returns {BOOL_LITERAL}:</p>{nlai}{h_emu_alg}")
class _:
    def s_nv(anode, env0):
        [cond, bool_lit, h_emu_alg] = anode.children
        tc_cond(cond, env0)
        # XXX should check h_emu_alg
        return None

@P(r"{EE_RULE} : It is a Syntax Error if {CONDITION}. Additional early error rules for {G_SYM} within direct eval are defined in {h_emu_xref}.")
@P(r"{EE_RULE} : It is a Syntax Error if {CONDITION}. Additional early error rules for {G_SYM} in direct eval are defined in {h_emu_xref}.")
class _:
    def s_nv(anode, env0):
        [cond, g_sym, h_emu_xref] = anode.children
        tc_cond(cond, env0)
        return None

@P(r"{EE_RULE} : It is a Syntax Error if {CONDITION}. This rule is not applied if {CONDITION}.")
class _:
    def s_nv(anode, env0):
        [conda, condb] = anode.children
        (t_env, f_env) = tc_cond(condb, env0)
        tc_cond(conda, f_env)
        return None

@P(r"{EE_RULE} : For each {nonterminal} {DEFVAR} in {NAMED_OPERATION_INVOCATION}: It is a Syntax Error if {CONDITION}.")
class _:
    def s_nv(anode, env0):
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

@P('{VAL_DESC} : a mathematical value')
class _:
    s_tb = T_MathReal_

@P('{VAL_DESC} : a non-negative extended mathematical value')
class _:
    s_tb = a_subset_of(T_MathReal_ | T_MathPosInfinity_)

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

@P(r'{SUM} : {TERM} {SUM_OPERATOR} {TERM}')
@P(r"{SUM} : {SUM} {SUM_OPERATOR} {TERM}")
@P(r'{PRODUCT} : {FACTOR} {PRODUCT_OPERATOR} {FACTOR}')
class _:
    def s_expr(expr, env0, _):
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
                (T_MathInteger_     , '+'      , T_MathPosInfinity_ ): T_MathPosInfinity_,

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
                (T_FiniteNumber_  , '×'      , T_IntegralNumber_): T_FiniteNumber_,
                (T_FiniteNumber_  , '+'      , T_FiniteNumber_  ): T_FiniteNumber_,
                (T_FiniteNumber_  , '+'      , T_IntegralNumber_): T_FiniteNumber_,
                (T_FiniteNumber_  , '-'      , T_FiniteNumber_  ): T_FiniteNumber_,
                (T_FiniteNumber_  , '-'      , T_IntegralNumber_): T_FiniteNumber_,
                (T_FiniteNumber_  , '/'      , T_FiniteNumber_  ): T_FiniteNumber_, # assuming that b isn't 0
                (T_IntegralNumber_, '/'      , T_FiniteNumber_  ): T_FiniteNumber_,
                (T_IntegralNumber_, '/'      , T_IntegralNumber_): T_FiniteNumber_, # assuming that b isn't 0

                (T_IntegralNumber_, '+', T_IntegralNumber_): T_IntegralNumber_,
                (T_IntegralNumber_, '-', T_IntegralNumber_): T_IntegralNumber_,
                (T_IntegralNumber_, '×', T_IntegralNumber_): T_IntegralNumber_,

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

        if expr.source_text() in ['(_x_ - _xDigit_) / 2', '(_y_ - _yDigit_) / 2']:
            # BigIntBitwiseOp
            assert result_t == T_MathReal_
            # However, _xDigit_ is _x_ mod 2,
            # so _x_ - _xDigit_ is even,
            # so (_x_ - _xDigit_) / 2 is actually MathInteger.
            result_t = T_MathInteger_

        return (result_t, env2)

@P(r"{PRODUCT} : {UNARY_OPERATOR}{FACTOR}")
class _:
    def s_expr(expr, env0, _):
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

@P(r'{EXPR} : the negative of {EX}')
class _:
    def s_expr(expr, env0, _):
        [ex] = expr.children
        (ex_t, env1) = tc_expr(ex, env0); assert env1 is env0
        assert ex_t == T_TBD or ex_t == T_MathInteger_
        return (ex_t, env0)

@P(r"{PRODUCT} : the negation of {EX}")
class _:
    def s_expr(expr, env0, _):
        [ex] = expr.children
        env0.assert_expr_is_of_type(ex, T_MathReal_)
        return (T_MathReal_, env0)

@P(r"{EX} : the remainder of dividing {EX} by {EX}")
@P(r"{EX} : The remainder of dividing {EX} by {EX}")
class _:
    def s_expr(expr, env0, _):
        [aex, bex] = expr.children
        env0.assert_expr_is_of_type(aex, T_MathInteger_)
        env0.assert_expr_is_of_type(bex, T_MathInteger_)
        return (T_MathInteger_, env0)

@P(r"{PRODUCT} : the quotient {FACTOR} / {FACTOR}")
class _:
    def s_expr(expr, env0, _):
        [vara, varb] = expr.children
        env1 = env0.ensure_expr_is_of_type(vara, T_MathReal_)
        env2 = env1.ensure_expr_is_of_type(varb, T_MathReal_)
        return (T_MathReal_, env2)

@P(r"{EX} : {EX}, rounding down to the nearest integer, including for negative numbers")
class _:
    def s_expr(expr, env0, _):
        [ex] = expr.children
        env0.assert_expr_is_of_type(ex, T_MathReal_)
        return (T_MathInteger_, env0)

@P(r"{FACTOR} : {BASE}<sup>{EX}</sup>")
class _:
    def s_expr(expr, env0, _):
        [base, exponent] = expr.children
        (base_t, env1) = tc_expr(base, env0); assert env1 is env0
        if base_t == T_MathInteger_:
            env1 = env0.ensure_expr_is_of_type(exponent, T_MathReal_ | T_BigInt)
        else:
            assert 0, base_t
        return (base_t, env1) # XXX unless exponent is negative

@P(r"{NUM_EXPR} : {EX} raised to the power {EX}")
class _:
    def s_expr(expr, env0, _):
        [a, b] = expr.children
        env0.assert_expr_is_of_type(a, T_MathInteger_)
        env0.assert_expr_is_of_type(b, T_MathInteger_)
        return (T_MathInteger_, env0) # unless exponent is negative

@P(r"{EXPR} : the result of raising {EX} to the {EX} power")
class _:
    def s_expr(expr, env0, _):
        [avar, bvar] = expr.children
        env1 = env0.ensure_expr_is_of_type(avar, T_MathReal_)
        env2 = env0.ensure_expr_is_of_type(bvar, T_MathReal_)
        return (T_MathReal_, env2)

@P(r'{NUM_EXPR} : π / 2')
@P(r'{NUM_EXPR} : π / 4')
@P(r'{NUM_EXPR} : π')
@P(r'{NUM_EXPR} : 3π / 4')
@P(r'{NUM_EXPR} : -π / 2')
@P(r'{NUM_EXPR} : -π / 4')
@P(r'{NUM_EXPR} : -π')
@P(r'{NUM_EXPR} : -3π / 4')
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_MathReal_, env0)

@P(r"{EXPR} : the result of the {MATH_FUNC} of {EX}")
class _:
    def s_expr(expr, env0, _):
        [math_func, ex] = expr.children
        env1 = env0.ensure_expr_is_of_type(ex, T_Number | T_MathReal_)
        return (T_MathReal_, env1)

@P(r"{EXPR} : the result of subtracting 1 from the exponential function of {EX}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_MathReal_)
        return (T_MathReal_, env1)

@P(r"{EXPR} : the square root of the sum of squares of the mathematical values of the elements of {var}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_List)
        return (T_MathReal_, env0)

@P(r"{EXPR} : an implementation-defined choice of either {var} or {var}")
class _:
    def s_expr(expr, env0, _):
        [vara, varb] = expr.children
        env0.assert_expr_is_of_type(vara, T_MathReal_)
        env0.assert_expr_is_of_type(varb, T_MathReal_)
        return (T_MathReal_, env0)

# comparisons:

@P(r'{CONDITION_1} : {var} is even')
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_MathInteger_)
        return (env0, env0)

@P(r'{NUM_COMPARISON} : {NUM_COMPARAND} {NUM_COMPARATOR} {NUM_COMPARAND} {NUM_COMPARATOR} {NUM_COMPARAND}')
class _:
    def s_cond(cond, env0, asserting):
        [a, _, b, _, c] = cond.children
        if '<sub>𝔽</sub>' in a.source_text(): # kludgey test
            env0.assert_expr_is_of_type(a, T_IntegralNumber_)
            env0.assert_expr_is_of_type(b, T_IntegralNumber_)
            env0.assert_expr_is_of_type(c, T_IntegralNumber_)
            return (env0, env0)
        else:
            env0.assert_expr_is_of_type(a, T_MathInteger_)
            env1 = env0.ensure_expr_is_of_type(b, T_MathInteger_ | T_MathNegInfinity_ | T_MathPosInfinity_)
            env0.assert_expr_is_of_type(c, T_MathInteger_)
            env2 = env1.with_expr_type_narrowed(b, T_MathInteger_)
            return (env2, env2)

@P(r"{NUM_COMPARISON} : {NUM_COMPARAND} {NUM_COMPARATOR} {NUM_COMPARAND}")
class _:
    def s_cond(cond, env0, asserting):
        [a, op, b] = cond.children
        (a_t, env1) = tc_expr(a, env0);
        (b_t, env2) = tc_expr(b, env1);
        op_st = op.source_text()

        assert a_t != T_0
        assert b_t != T_0

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
                    (T_MathNegInfinity_, '='   , T_MathNegInfinity_): 'T',
                    (T_MathPosInfinity_, '='   , T_MathPosInfinity_): 'T',
                    (T_MathPosInfinity_, '>'   , T_FiniteNumber_   ): 'T',
                    (T_MathPosInfinity_, '>'   , T_MathInteger_    ): 'T',
                    (T_MathPosInfinity_, '≥'   , T_MathInteger_    ): 'T',

                    # always false:
                    (T_MathNegInfinity_, '≥'   , T_MathInteger_): 'F',
                    (T_MathNegInfinity_, '='   , T_MathInteger_): 'F',
                    (T_MathNegInfinity_, '='   , T_MathPosInfinity_): 'F',
                    (T_MathPosInfinity_, '≤'   , T_MathInteger_): 'F',
                    (T_MathPosInfinity_, '&lt;', T_MathInteger_): 'F',
                    (T_MathPosInfinity_, '='   , T_MathInteger_): 'F',
                    (T_MathPosInfinity_, '='   , T_MathNegInfinity_): 'F',
                    (T_MathInteger_    , '='   , T_MathNegInfinity_): 'F',
                    (T_MathInteger_    , '='   , T_MathPosInfinity_): 'F',
                    (T_MathInteger_    , '≥'   , T_MathPosInfinity_): 'F',

                    # can be true or false:
                    (T_ExtendedMathReal_, '≥'   , T_MathInteger_     ): 'TF',
                    (T_ExtendedMathReal_, '≤'   , T_MathInteger_     ): 'TF',
                    (T_ExtendedMathReal_, '&lt;', T_ExtendedMathReal_): 'TF',
                    (T_ExtendedMathReal_, '&lt;', T_MathInteger_     ): 'TF',
                    (T_MathInteger_     , '≥'   , T_MathInteger_     ): 'TF',
                    (T_MathInteger_     , '≥'   , T_MathReal_        ): 'TF',
                    (T_MathInteger_     , '>'   , T_MathInteger_     ): 'TF',
                    (T_MathInteger_     , '≤'   , T_MathInteger_     ): 'TF',
                    (T_MathInteger_     , '&lt;', T_ExtendedMathReal_): 'TF',
                    (T_MathInteger_     , '&lt;', T_MathInteger_     ): 'TF',
                    (T_MathInteger_     , '≠'   , T_MathInteger_     ): 'TF',
                    (T_MathInteger_     , '≠'   , T_MathReal_        ): 'TF',
                    (T_MathInteger_     , '='   , T_MathInteger_     ): 'TF',
                    (T_MathReal_        , '≤'   , T_MathInteger_     ): 'TF',
                    (T_MathReal_        , '≥'   , T_MathInteger_     ): 'TF',
                    (T_MathReal_        , '>'   , T_MathInteger_     ): 'TF',
                    (T_MathReal_        , '>'   , T_MathReal_        ): 'TF',
                    (T_MathReal_        , '&lt;', T_MathInteger_     ): 'TF',
                    (T_MathReal_        , '&lt;', T_MathReal_        ): 'TF',
                    (T_MathReal_        , '≠'   , T_MathInteger_     ): 'TF',
                    (T_MathReal_        , '='   , T_MathInteger_     ): 'TF',
                    (T_MathReal_        , '='   , T_MathReal_        ): 'TF',

                    (T_MathInteger_     , 'is greater than or equal to', T_MathInteger_): 'TF',
                    (T_MathInteger_     , 'is strictly greater than'   , T_MathInteger_): 'TF',

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
                    (T_IntegralNumber_         , '≤'   , T_IntegralNumber_         ): 'TF',
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

@P(r'{CONDITION_1} : {var} is as small as possible')
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_MathInteger_)
        return (env0, env0)

# ------------------------------------------------------------------------------
#> This specification denotes most numeric values in base 10;
#> it also uses numeric values of the form 0x followed by digits 0-9 or A-F as base-16 values.

@P(r"{dec_int_lit} : \b [0-9]+ (?![0-9A-Za-z])")
class _:
    def s_expr(expr, env0, _):
        return (T_MathNonNegativeInteger_, env0)

@P('{MATH_LITERAL} : {dec_int_lit}')
class _:
    s_tb = a_subset_of(T_MathInteger_)

    def s_expr(expr, env0, _):
        [lit] = expr.children
        return (T_MathInteger_, env0)

@P(r"{MATH_LITERAL} : {hex_int_lit}")
@P(r"{BASE} : 10")
@P(r"{BASE} : 2")
class _:
    def s_expr(expr, env0, _):
        # [] = expr.children
        return (T_MathInteger_, env0)

@P(r"{MATH_LITERAL} : 64 (that is, 8<sup>2</sup>)")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_MathInteger_, env0)

@P(r"{MATH_LITERAL} : 8.64")
@P(r"{MATH_LITERAL} : 0.5")
class _:
    def s_expr(expr, env0, _):
        return (T_MathReal_, env0)

@P(r"{MATH_LITERAL} : +&infin;")
@P(r"{MATH_LITERAL} : +∞")
class _:
    s_tb = T_MathPosInfinity_

    def s_expr(expr, env0, _):
        return (T_MathPosInfinity_, env0)

@P(r"{MATH_LITERAL} : -&infin;")
@P(r"{MATH_LITERAL} : -∞")
class _:
    s_tb = T_MathNegInfinity_

    def s_expr(expr, env0, _):
        return (T_MathNegInfinity_, env0)

# ------------------------------------------------------------------------------
#> When the term <dfn>integer</dfn> is used in this specification,
#> it refers to a mathematical value which is in the set of integers,
#> unless otherwise stated.

@P('{VAL_DESC} : an integer')
class _:
    s_tb = T_MathInteger_

@P('{VAL_DESC} : an integer ≥ {dsb_word}')
class _:
    s_tb = a_subset_of(T_MathInteger_)

@P('{VAL_DESC} : a non-negative integer that is evenly divisible by 4')
class _:
    s_tb = a_subset_of(T_MathNonNegativeInteger_)

@P('{VAL_DESC} : a non-negative integer')
class _:
    s_tb = T_MathNonNegativeInteger_ # currently mapped to MathInteger_

@P('{VAL_DESC} : a positive integer')
class _:
    s_tb = a_subset_of(T_MathNonNegativeInteger_)

# ------------------------------------------------------------------------------
#> When the term <dfn>integral Number</dfn> is used in this specification,
#> it refers to a Number value whose mathematical value is in the set of integers.

@P('{VAL_DESC} : an integral Number')
class _:
    s_tb = T_IntegralNumber_

@P('{VAL_DESC} : an odd integral Number')
class _:
    s_tb = a_subset_of(T_IntegralNumber_)

@P('{VAL_DESC} : a non-negative integral Number')
class _:
    s_tb = a_subset_of(T_IntegralNumber_)

@P('{VAL_DESC} : a non-negative finite Number')
class _:
    s_tb = a_subset_of(T_FiniteNumber_)

# ------------------------------------------------------------------------------
#> Conversions between mathematical values and Numbers or BigInts
#> are always explicit in this document.
#> ...
#> A conversion from a Number or BigInt _x_ to a mathematical value
#>     is denoted as "the <dfn>mathematical value of</dfn> _x_",
#>     or <emu-eqn>ℝ(_x_)</emu-eqn>.
#> The mathematical value of *+0*<sub>𝔽</sub> and *-0*<sub>𝔽</sub>
#>     is the mathematical value 0.
#> The mathematical value of non-finite values is not defined.
#> The <dfn>extended mathematical value of</dfn> _x_
#>     is the mathematical value of _x_ for finite values,
#>     and is +∞ and -∞ for *+∞*<sub>𝔽</sub> and *-∞*<sub>𝔽</sub> respectively;
#>     it is not defined for *NaN*.

@P('{EXPR} : the extended mathematical value of {var}')
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_FiniteNumber_ | T_PosInfinityNumber_ | T_NegInfinityNumber_)
        return (T_ExtendedMathReal_, env0)

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

@P(r"{EXPR} : the result of clamping {var} between 0 and {EX}")
class _:
    def s_expr(expr, env0, _):
        [var, upper_ex] = expr.children
        env0.assert_expr_is_of_type(upper_ex, T_MathInteger_)
        (var_t, env1) = tc_expr(var, env0)
        if var_t == T_ExtendedMathReal_:
            result_t = T_MathReal_
        elif var_t == T_MathInteger_ | T_MathNegInfinity_ | T_MathPosInfinity_:
            result_t = T_MathInteger_
        else:
            assert 0, var_t
        return (result_t, env0)

# ------------------------------------------------------------------------------
#> An <dfn>interval</dfn> from lower bound _a_ to upper bound _b_
#> is a possibly-infinite, possibly-empty set of numeric values of the same numeric type.
#> Each bound will be described as either inclusive or exclusive, but not both.

@P(r"{INTERVAL} : the inclusive interval from {EX} to {EX}")
@P(r"{INTERVAL} : the interval from {EX} (inclusive) to {EX} (exclusive)")
class _:
    def s_expr(expr, env0, _):
        [lo, hi] = expr.children
        env0.assert_expr_is_of_type(lo, T_MathInteger_)
        env0.assert_expr_is_of_type(hi, T_MathInteger_)
        return (T_MathInteger_, env0)
        # Should maybe be ListType(T_MathInteger_) or something similar

@P(r"{CONDITION_1} : {var} is in {INTERVAL}")
@P(r"{CONDITION_1} : {var} is not in {INTERVAL}")
class _:
    def s_cond(cond, env0, asserting):
        [var, interval] = cond.children
        env1 = env0.ensure_expr_is_of_type(var, T_MathInteger_)
        env1.assert_expr_is_of_type(interval, T_MathInteger_)
        return (env1, env1)

@P(r"{CONDITION_1} : there exists an integer {DEFVAR} in {INTERVAL} such that {CONDITION_1}")
class _:
    def s_cond(cond, env0, asserting):
        [i_var, interval, stcond] = cond.children
        env0.assert_expr_is_of_type(interval, T_MathInteger_)
        env_for_cond = env0.plus_new_entry(i_var, T_MathInteger_)
        return tc_cond(stcond, env_for_cond)

@P(r"{CONDITION_1} : {SETTABLE} ≠ {SETTABLE} for some integer {DEFVAR} in {INTERVAL}")
class _:
    def s_cond(cond, env0, asserting):
        [seta, setb, let_var, interval] = cond.children
        env0.assert_expr_is_of_type(interval, T_MathInteger_)
        env_for_settables = env0.plus_new_entry(let_var, T_MathInteger_)
        env_for_settables.assert_expr_is_of_type(seta, T_MathInteger_)
        env_for_settables.assert_expr_is_of_type(setb, T_MathInteger_)
        return (env0, env0)

@P('{VAL_DESC} : an integer in {INTERVAL}')
class _:
    def s_tb(val_desc, env):
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

@P(r"{EACH_THING} : integer {DEFVAR} in {INTERVAL}")
class _:
    def s_nv(each_thing, env0):
        [loop_var, interval] = each_thing.children
        env0.assert_expr_is_of_type(interval, T_MathInteger_)
        return env0.plus_new_entry(loop_var, T_MathInteger_)

@P(r"{EXPR} : a List of the integers in {INTERVAL}, in ascending order")
@P(r"{EXPR} : a List of the integers in {INTERVAL}, in descending order")
class _:
    def s_expr(expr, env0, _):
        [interval] = expr.children
        env0.assert_expr_is_of_type(interval, T_MathNonNegativeInteger_)
        return (ListType(T_MathNonNegativeInteger_), env0)

# ------------------------------------------------------------------------------
# (The spec should talk about bit strings somewhere.)

@P(r"{EXPR} : the number of leading 1 bits in {var}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_MathNonNegativeInteger_)
        return (T_MathNonNegativeInteger_, env0)

@P(r"{EX} : the integer represented by the 32-bit two's complement bit string {var}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_MathInteger_) # bit string
        return (T_MathInteger_, env0)

@P(r'{EXPR} : the byte elements of {var} concatenated and interpreted as a bit string encoding of an unsigned little-endian binary number')
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_MathInteger_))
        return (T_MathInteger_, env1)

@P(r"{EXPR} : the byte elements of {var} concatenated and interpreted as a bit string encoding of a binary little-endian two's complement number of bit length {PRODUCT}")
class _:
    def s_expr(expr, env0, _):
        [var, product] = expr.children
        env1 = env0.ensure_expr_is_of_type(product, T_MathInteger_ | T_Number); assert env1 is env0
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_MathInteger_))
        return (T_MathInteger_, env1)

@P(r'{EXPR} : the byte elements of {var} concatenated and interpreted as a little-endian bit string encoding of an IEEE 754-2019 binary32 value')
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_MathInteger_))
        return (T_IEEE_binary32_, env1)

@P(r'{EXPR} : the byte elements of {var} concatenated and interpreted as a little-endian bit string encoding of an IEEE 754-2019 binary64 value')
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_MathInteger_))
        return (T_IEEE_binary64_, env1)

@P(r"{EXPR} : the result of applying the bitwise AND operation to {var} and {var}")
@P(r"{EXPR} : the result of applying the bitwise exclusive OR (XOR) operation to {var} and {var}")
@P(r"{EXPR} : the result of applying the bitwise inclusive OR operation to {var} and {var}")
class _:
    def s_expr(expr, env0, _):
        [x, y] = expr.children
        env0.assert_expr_is_of_type(x, T_MathInteger_) # "bit string"
        env0.assert_expr_is_of_type(y, T_MathInteger_) # "bit string"
        return (T_MathInteger_, env0) # "bit string"

@P(r"{EXPR} : the 32-bit two's complement bit string representing {EX}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_MathInteger_)
        return (T_MathInteger_, env0) # bit string

@P(r'{EXPR} : a List whose elements are the {var}-byte binary encoding of {var}. The bytes are ordered in little endian order')
@P(r"{EXPR} : a List whose elements are the {var}-byte binary two's complement encoding of {var}. The bytes are ordered in little endian order")
class _:
    def s_expr(expr, env0, _):
        [n_var, v_var] = expr.children
        env0.assert_expr_is_of_type(n_var, T_MathNonNegativeInteger_)
        env0.assert_expr_is_of_type(v_var, T_MathNonNegativeInteger_)
        return (ListType(T_MathInteger_), env0)

# ------------------------------------------------------------------------------
# (Although the spec goes into detail about
# the mappings from string-ish to numeric and numeric to String,
# it also assumes such mappings for simple cases.)

@P(r"{EX} : the digits of the decimal representation of {var} (in order, with no leading zeroes)")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_MathInteger_)
        return (ListType(T_code_unit_), env0)

@P(r"{EXPR} : the mathematical value denoted by the result of replacing each significant digit in the decimal representation of {var} after the 20th with a 0 digit")
@P(r"{EXPR} : the mathematical value denoted by the result of replacing each significant digit in the decimal representation of {var} after the 20th with a 0 digit and then incrementing it at the 20th position (with carrying as necessary)")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_MathReal_)
        return (T_MathReal_, env0)

@P(r"{CONDITION_1} : the decimal representation of {var} has 20 or fewer significant digits")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_MathReal_)
        return (env0, env0)

@P(r"{EXPR} : the String representation of {EX}, formatted as a decimal number")
@P(r"{EXPR} : the String representation of {EX}, formatted as a lowercase hexadecimal number")
@P(r"{EXPR} : the String representation of {EX}, formatted as an uppercase hexadecimal number")
class _:
    def s_expr(expr, env0, _):
        [ex] = expr.children
        env1 = env0.ensure_expr_is_of_type(ex, T_Number | T_MathInteger_)
        return (T_String, env1)

# ==============================================================================
#@ 5.2.6 Value Notation

#> Values which are internal to the specification
#> and not directly observable from ECMAScript code
#> are indicated with a ~sans-serif~ typeface.

@P(r"{LITERAL} : {tilded_word}")
class _:
    def s_tb(literal, env):
        [tilded_word] = literal.children
        return type_for_tilded_word(tilded_word)

    def s_expr(expr, env0, _):
        [tilded_word] = expr.children
        return (type_for_tilded_word(tilded_word), env0)

def type_for_tilded_word(tilded_word):
    assert tilded_word.prod.lhs_s == '{tilded_word}'
    [chars] = tilded_word.children
    assert chars[0] == '~'
    assert chars[-1] == '~'
    uchars = chars[1:-1].replace('-', '_').replace('+', '_')
    return HierType(f"tilde_{uchars}_")

# ==============================================================================
#@ 5.2.7 Identity

#> In this specification,
#> the word “is” is used to compare two values through equality,
#> as in “If _bool_ is *true*, then”.

# (So I'm putting all the "X is Y" forms here.)

@P(r"{CONDITION_1} : {EX} is not {PREFIX_PAREN}")
@P(r"{CONDITION_1} : {EX} is not {SETTABLE}")
@P(r"{CONDITION_1} : {EX} is {PREFIX_PAREN}")
@P(r"{CONDITION_1} : {EX} is {SETTABLE}")
class _:
    def s_cond(cond, env0, asserting):
        [exa, exb] = cond.children
        (exa_type, env1) = tc_expr(exa, env0)
        (exb_type, env2) = tc_expr(exb, env1)
        if exa_type == exb_type:
            # good
            return (env2, env2)

        # If one side has type TBD,
        # give it the same type as the other side.
        # Its actual type might be wider,
        # but this is presumably a good start.
        elif exa_type == T_TBD:
            env3 = env2.with_expr_type_replaced(exa, exb_type)
            return (env3, env3)
        elif exb_type == T_TBD:
            env3 = env2.with_expr_type_replaced(exb, exa_type)
            return (env3, env3)

        else:
            (common_t, _) = exa_type.split_by(exb_type)
            assert common_t != T_0
            # In the world where the two sides are equal,
            # they must both have a type that's the intersection of the two
            is_env = ( env2
                .with_expr_type_narrowed(exa, common_t)
                .with_expr_type_narrowed(exb, common_t)
            )
            # In the world where the two sides are different,
            # they keep their old types.

            if 'not' in cond.prod.rhs_s:
                # X is not Y
                t_env = env2
                f_env = is_env
            else:
                # X is T
                t_env = is_env
                f_env = env2
            return (t_env, f_env)

@P(r"{CONDITION_1} : {EX} and {EX} are distinct values")
class _:
    def s_cond(cond, env0, asserting):
        [exa, exb] = cond.children
        (exa_type, env1) = tc_expr(exa, env0)
        (exb_type, env2) = tc_expr(exb, env1)
        return (env2, env2)

# ------

@P(r'{CONDITION_1} : {EX} and {EX} are both {LITERAL}')
class _:
    def s_cond(cond, env0, asserting):
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

@P(r'{CONDITION_1} : {EX} and {EX} are both {LITERAL} or both {LITERAL}')
class _:
    def s_cond(cond, env0, asserting):
        # occurs once, in SameValueNonNumber
        [exa, exb, litc, litd] = cond.children
        assert litc.source_text() == '*true*'
        assert litd.source_text() == '*false*'
        enva = env0.ensure_expr_is_of_type(exa, T_Boolean); assert enva is env0
        envb = env0.ensure_expr_is_of_type(exb, T_Boolean); # assert envb is env0
        return (envb, envb)

@P(r"{CONDITION_1} : {var} or {var} is {LITERAL}")
@P(r"{CONDITION_1} : either {DOTTING} or {DOTTING} is {LITERAL}")
class _:
    def s_cond(cond, env0, asserting):
        [v1, v2, lit] = cond.children
        (t1, env1) = tc_expr(v1, env0); assert env1 is env0
        (t2, env2) = tc_expr(v2, env0); assert env2 is env0
        assert t1 == t2
        env0.assert_expr_is_of_type(lit, t1)
        return (env0, env0)

# ------

@P(r"{CONDITION_1} : {EX} is also {VAL_DESC}")
@P(r"{CONDITION_1} : {EX} is never {VAL_DESC}")
@P(r"{CONDITION_1} : {EX} is not {VALUE_DESCRIPTION}")
@P(r"{CONDITION_1} : {EX} is {VALUE_DESCRIPTION}")
class _:
    def s_cond(cond, env0, asserting):
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
        # (We wouldn't need this if we changed all
        # `_cr_.[[Type]] is ~foo~` to `_cr_ is a foo completion`.)
        while True: # ONCE
            dotting = ex.is_a('{DOTTING}')
            if dotting is None: break
            (lhs, dsbn) = dotting.children
            dsbn_name = dsbn.source_text()
            if dsbn_name != '[[Type]]': break
            t = type_corresponding_to_comptype_literal(vd)
            return env0.with_type_test(lhs, copula, t, asserting)

        (sub_t, sup_t) = type_bracket_for(vd, env0)
        return env0.with_type_test(ex, copula, [sub_t, sup_t], asserting)

@P(r"{CONDITION_1} : {EX} is neither {VAL_DESC} nor {VAL_DESC} nor {VAL_DESC}")
@P(r"{CONDITION_1} : {EX} is neither {VAL_DESC} nor {VAL_DESC}")
class _:
    def s_cond(cond, env0, asserting):
        [ex, *vds] = cond.children

        sub_t = T_0
        sup_t = T_0
        for vd in vds:
            (x_sub_t, x_sup_t) = type_bracket_for(vd, env0)
            sub_t |= x_sub_t
            sup_t |= x_sup_t

        return env0.with_type_test(ex, 'isnt a', [sub_t, sup_t], asserting)

    # -------

@P('{VALUE_DESCRIPTION} : either {VAL_DESC} or {VAL_DESC}')
@P('{VALUE_DESCRIPTION} : either {VAL_DESC}, or {VAL_DESC}')
@P('{VALUE_DESCRIPTION} : either {VAL_DESC}, {VAL_DESC}, or {VAL_DESC}')
@P('{VALUE_DESCRIPTION} : either {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, or {VAL_DESC}')
@P('{VALUE_DESCRIPTION} : either {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, or {VAL_DESC}')
@P('{VALUE_DESCRIPTION} : one of {VAL_DESC}, {VAL_DESC}, or {VAL_DESC}')
@P('{VALUE_DESCRIPTION} : one of {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, or {VAL_DESC}')
@P('{VALUE_DESCRIPTION} : one of {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC} or {VAL_DESC}')
@P('{VALUE_DESCRIPTION} : one of {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, or {VAL_DESC}')
@P('{VALUE_DESCRIPTION} : one of {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, or {VAL_DESC}')
@P('{VALUE_DESCRIPTION} : one of {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, or {VAL_DESC}')
@P('{VALUE_DESCRIPTION} : one of {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, or {VAL_DESC}')
@P('{VALUE_DESCRIPTION} : one of {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, or {VAL_DESC}')
@P('{VALUE_DESCRIPTION} : {VAL_DESC} or {VAL_DESC}')
@P('{VALUE_DESCRIPTION} : {VAL_DESC}, {VAL_DESC}, or {VAL_DESC}')
@P('{VALUE_DESCRIPTION} : {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, or {VAL_DESC}')
@P('{VALUE_DESCRIPTION} : {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, or {VAL_DESC}')
@P('{VALUE_DESCRIPTION} : {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, or {VAL_DESC}')
@P('{VALUE_DESCRIPTION} : {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, or {VAL_DESC}')
@P('{VALUE_DESCRIPTION} : {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, or {VAL_DESC}')
class _:
    def s_tb(value_description, env):
        result_sub_t = T_0
        result_sup_t = T_0
        for val_desc in value_description.children:
            (sub_t, sup_t) = type_bracket_for(val_desc, env)
            result_sub_t |= sub_t
            result_sup_t |= sup_t
        return (result_sub_t, result_sup_t)

@P('{VALUE_DESCRIPTION} : {VAL_DESC}, but not {VALUE_DESCRIPTION}')
class _:
    def s_tb(value_description, env):
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

@P('{VAL_DESC} : a {h_emu_xref}')
class _:
    def s_tb(val_desc, env):
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

@P(r'{TYPE_TEST} : Type({TYPE_ARG}) is Type({TYPE_ARG})')
@P(r'{TYPE_TEST} : Type({TYPE_ARG}) is not Type({TYPE_ARG})')
class _:
    def s_cond(cond, env0, asserting):
        # Env can't represent the effect of these.
        # If the incoming static types were different,
        # the 'true' env could at least narrow those to their intersection,
        # but the form only appears twice, and in both cases the static types are the same.
        return (env0, env0)

@P(r"{CONDITION_1} : {var} does not contain Type({TYPE_ARG})")
class _:
    def s_cond(cond, env0, asserting):
        # once, in CreateListFromArrayLike
        [var, type_arg] = cond.children
        env0.assert_expr_is_of_type(var, ListType(T_LangTypeName_))
        return (env0, env0)

@P(r"{LITERAL} : {TYPE_NAME}")
class _:
    def s_expr(expr, env0, _):
        [type_name] = expr.children
        return (T_LangTypeName_, env0)

@P('{VAL_DESC} : anything')
class _:
    s_tb = T_host_defined_

# ==============================================================================
#@ 6.1 ECMAScript Language Types

@P('{VAL_DESC} : an ECMAScript language value')
class _:
    s_tb = T_Tangible_

@P('{LIST_ELEMENTS_DESCRIPTION} : ECMAScript language values')
class _:
    s_tb = T_Tangible_

@P('{LIST_ELEMENTS_DESCRIPTION} : names of ECMAScript Language Types')
class _:
    s_tb = T_LangTypeName_

# ==============================================================================
#@ 6.1.1 The Undefined Type

@P(r'{LITERAL} : *undefined*')
class _:
    s_tb = T_Undefined

    def s_expr(expr, env0, _):
        return (T_Undefined, env0)

# ==============================================================================
#@ 6.1.2 The Null Type

@P(r'{LITERAL} : *null*')
class _:
    s_tb = T_Null

    def s_expr(expr, env0, _):
        return (T_Null, env0)

# ==============================================================================
#@ 6.1.3 The Boolean Type

@P('{VAL_DESC} : a Boolean')
class _:
    s_tb = T_Boolean

@P('{LITERAL} : {BOOL_LITERAL}')
class _:
    s_tb = a_subset_of(T_Boolean)

    def s_expr(expr, env0, _):
        return (T_Boolean, env0)

# ==============================================================================
#@ 6.1.4 The String Type

# ------------------------------------------------------------------------------
#> The <dfn>String type</dfn> is the set of all ordered sequences
#> of zero or more 16-bit unsigned integer values (“elements”)
#> up to a maximum length of 2<sup>53</sup> - 1 elements.
#> The String type is generally used to represent textual data in a running ECMAScript program,
#> in which case each element in the String is treated as a UTF-16 code unit value.

@P('{VAL_DESC} : a String')
class _:
    s_tb = T_String

@P('{LIST_ELEMENTS_DESCRIPTION} : Strings')
class _:
    s_tb = T_String

@P('{LIST_ELEMENTS_DESCRIPTION} : either Strings or *null*')
class _:
    s_tb = T_String | T_Null

@P('{LIST_ELEMENTS_DESCRIPTION} : either Strings or *undefined*')
class _:
    s_tb = T_String | T_Undefined

@P(r'{LITERAL} : {STR_LITERAL}')
class _:
    s_tb = a_subset_of(T_String)

    def s_expr(expr, env0, _):
        return (T_String, env0)

@P(r'{STR_LITERAL} : *","* (a comma)')
@P(r'{STR_LITERAL} : the empty String')
@P(r'{STR_LITERAL} : {starred_str}')
@P(r'{STR_LITERAL} : {starred_str} ({code_unit_lit} followed by {code_unit_lit})')
class _:
    def s_expr(expr, env0, _):
        return (T_String, env0)

@P(r"{EX} : the String {var}")
@P(r"{EXPR} : the String value {SETTABLE}")
class _:
    def s_expr(expr, env0, _):
        [ex] = expr.children
        env0.ensure_expr_is_of_type(ex, T_String)
        return (T_String, env0)

@P("{EX} : {h_code_quote}")
class _:
    def s_expr(expr, env0, _):
        [h_code_quote] = expr.children
        return (T_String, env0)

@P(r"{EXPR} : {var}'s single code unit element") # todo: element of String
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_String)
        return (T_code_unit_, env1)

@P(r'{EX} : the first code unit of {var}')
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_String)
        return (T_code_unit_, env1)

# ----

@P(r'{CONDITION_1} : {var} contains any code unit more than once')
@P(r'{CONDITION_1} : {var} contains any code unit other than *"d"*, *"g"*, *"i"*, *"m"*, *"s"*, *"u"*, or *"y"*')
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_String)
        return (env0, env0)

@P(r"{CONDITION_1} : {var} contains a code unit that is not a radix-{var} digit")
class _:
    def s_cond(cond, env0, asserting):
        [svar, rvar] = cond.children
        env0.assert_expr_is_of_type(svar, T_String)
        env0.assert_expr_is_of_type(rvar, T_MathInteger_)
        return (env0, env0)

@P(r"{CONDITION_1} : {var} starts with {STR_LITERAL}")
class _:
    def s_cond(cond, env0, asserting):
        [var, str_literal] = cond.children
        env0.assert_expr_is_of_type(var, T_String)
        return (env0, env0)

@P(r"{CONDITION_1} : {var} starts with {STR_LITERAL} followed by {EX} or more decimal digits")
class _:
    def s_cond(cond, env0, asserting):
        [var, str_literal, ex] = cond.children
        env0.assert_expr_is_of_type(var, T_String)
        env0.assert_expr_is_of_type(ex, T_MathNonNegativeInteger_)
        return (env0, env0)

@P(r"{CONDITION_1} : the first two code units of {var} are either {STR_LITERAL} or {STR_LITERAL}")
class _:
    def s_cond(cond, env0, asserting):
        [var, lita, litb] = cond.children
        env0.assert_expr_is_of_type(var, T_String)
        env0.assert_expr_is_of_type(lita, T_String)
        env0.assert_expr_is_of_type(litb, T_String)
        return (env0, env0)

@P(r'{CONDITION_1} : {var} and {var} have the same length and the same code units in the same positions')
class _:
    def s_cond(cond, env0, asserting):
        # occurs once, in SameValueNonNumber
        [vara, varb] = cond.children
        enva = env0.ensure_expr_is_of_type(vara, T_String); assert enva is env0
        envb = env0.ensure_expr_is_of_type(varb, T_String); # assert envb is env0
        return (envb, envb)

# ------------------------------------------------------------------------------
#> Each element is regarded as occupying a position within the sequence.
#> These positions are indexed with non-negative integers.
#> The first element (if any) is at index 0, the next element (if any) at index 1, and so on.

@P(r"{EX} : the code unit at index {EX} within {EX}")
class _:
    def s_expr(expr, env0, _):
        [index_ex, str_ex] = expr.children
        env0.assert_expr_is_of_type(str_ex, T_String)
        env1 = env0.ensure_expr_is_of_type(index_ex, T_MathInteger_)
        return (T_code_unit_, env1)

@P(r"{EXPR} : the index within {var} of the first such code unit")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_String)
        return (T_MathNonNegativeInteger_, env0)

# ------------------------------------------------------------------------------
#> The length of a String is the number of elements (i.e., 16-bit values) within it.
#> The empty String has length zero and therefore contains no elements.

@P(r"{NUM_COMPARAND} : the length of {var}")
@P(r"{EX} : the length of {var}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_String)
        return (T_MathNonNegativeInteger_, env1)

# ------------------------------------------------------------------------------
#> In this specification,
#> the phrase "the <dfn>string-concatenation</dfn> of _A_, _B_, ..."
#> (where each argument is a String value, a code unit, or a sequence of code units)
#> denotes the String value whose sequence of code units
#> is the concatenation of the code units (in order) of each of the arguments (in order).

@P(r"{MULTILINE_EXPR} : the string-concatenation of:{I_BULLETS}")
class _:
    def s_expr(expr, env0, _):
        [bullets] = expr.children
        # Should check the bullets
        return (T_String, env0)

@P(r"{EXPR} : the string-concatenation of {EX} and {EX}")
@P(r"{EXPR} : the string-concatenation of {EX}, {EX}, and {EX}")
@P(r"{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, and {EX}")
@P(r"{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, {EX}, and {EX}")
@P(r"{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, {EX}, {EX}, and {EX}")
@P(r"{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, and {EX}")
@P(r"{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, and {EX}")
@P(r"{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, and {EX}")
@P(r"{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, and {EX}")
@P(r"{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, and {EX}")
class _:
    def s_expr(expr, env0, _):
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

@P(r"{EX} : the substring of {var} from {EX} to {EX}")
class _:
    def s_expr(expr, env0, _):
        [s_var, start_var, end_var] = expr.children
        env0.assert_expr_is_of_type(s_var, T_String)
        env1 = env0.ensure_expr_is_of_type(start_var, T_MathNonNegativeInteger_)
        env2 = env1.ensure_expr_is_of_type(end_var, T_MathNonNegativeInteger_)
        return (T_String, env2)

@P(r"{EX} : the substring of {var} from index {dec_int_lit}")
@P(r"{EX} : the substring of {var} from {EX}")
class _:
    def s_expr(expr, env0, _):
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

@P(r'{STR_LITERAL} : the ASCII word characters')
class _:
    def s_expr(expr, env0, _):
        return (T_String, env0)

# ------------------------------------------------------------------------------
# Other ways to specify a String value:

@P(r"{EX} : the first {SUM} code units of {var}")
class _:
    def s_expr(expr, env0, _):
        [summ, var] = expr.children
        env0.assert_expr_is_of_type(var, T_String)
        env1 = env0.ensure_expr_is_of_type(summ, T_MathInteger_)
        return (T_String, env1)

@P(r"{EX} : the remaining {EX} code units of {var}")
@P(r"{EXPR} : the other {EX} code units of {var}")
class _:
    def s_expr(expr, env0, _):
        [ex, var] = expr.children
        env0.assert_expr_is_of_type(var, T_String)
        env1 = env0.ensure_expr_is_of_type(ex, T_MathInteger_)
        return (T_String, env1)

@P(r"{EXPR} : the String value consisting solely of {code_unit_lit}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_code_unit_)
        return (T_String, env1)

@P(r"{EXPR} : the String value consisting of {EX}")
class _:
    def s_expr(expr, env0, _):
        [ex] = expr.children
        env1 = env0.ensure_expr_is_of_type(ex, T_code_unit_ | ListType(T_code_unit_))
        return (T_String, env1)

@P(r"{EXPR} : the String value that is a copy of {var} with both leading and trailing white space removed")
@P(r"{EXPR} : the String value that is a copy of {var} with leading white space removed")
@P(r"{EXPR} : the String value that is a copy of {var} with trailing white space removed")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_String)
        return (T_String, env0)

@P(r"{EXPR} : the String value that is the same as {var} except that each occurrence of {code_unit_lit} in {var} has been replaced with the six code unit sequence {STR_LITERAL}")
class _:
    def s_expr(expr, env0, _):
        [var, lita, var2, litb] = expr.children
        assert var.children == var2.children
        env1 = env0.ensure_expr_is_of_type(var, T_String)
        return (T_String, env1)

@P(r"{EXPR} : the String value that is the result of normalizing {var} into the normalization form named by {var} as specified in {h_a}")
class _:
    def s_expr(expr, env0, _):
        [s_var, nf_var, h_a] = expr.children
        env0.assert_expr_is_of_type(s_var, T_String)
        env0.assert_expr_is_of_type(nf_var, T_String)
        return (T_String, env0)

@P(r"{EXPR} : the String value containing {var} occurrences of {code_unit_lit}")
class _:
    def s_expr(expr, env0, _):
        [n, lit] = expr.children
        env0.assert_expr_is_of_type(lit, T_code_unit_)
        return (T_String, env0)

@P(r"{EXPR} : the String value that is made from {var} copies of {var} appended together")
class _:
    def s_expr(expr, env0, _):
        [n_var, s_var] = expr.children
        env0.assert_expr_is_of_type(s_var, T_String)
        env1 = env0.ensure_expr_is_of_type(n_var, T_MathInteger_)
        return (T_String, env1)

@P(r"{EXPR} : the String value consisting of repeated concatenations of {EX} truncated to length {var}")
class _:
    def s_expr(expr, env0, _):
        [ex, var] = expr.children
        env0.assert_expr_is_of_type(ex, T_String)
        env1 = env0.ensure_expr_is_of_type(var, T_MathInteger_)
        return (T_String, env1)

@P(r"{EXPR} : the String value formed by concatenating all the element Strings of {var} with each adjacent pair of Strings separated with {code_unit_lit}. A comma is not inserted either before the first String or after the last String")
class _:
    def s_expr(expr, env0, _):
        [var, str_literal] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_String))
        return (T_String, env1)

@P(r"{EXPR} : the String value formed by concatenating all the element Strings of {var} with each adjacent pair of Strings separated with {var}. The {var} String is not inserted either before the first String or after the last String")
class _:
    def s_expr(expr, env0, _):
        [var, sep_var, sep_var2] = expr.children
        assert sep_var.children == sep_var2.children
        env0.assert_expr_is_of_type(sep_var, T_String)
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_String))
        return (T_String, env1)

@P(r"{EXPR} : the String value whose code units are the elements of the List {var}. If {var} has no elements, the empty String is returned")
class _:
    def s_expr(expr, env0, _):
        [list_var, list_var2] = expr.children
        assert same_source_text(list_var, list_var2)
        env0.assert_expr_is_of_type(list_var, ListType(T_code_unit_))
        return (T_String, env0)

@P(r"{EXPR} : the implementation-defined list-separator String value appropriate for the host environment's current locale (such as {STR_LITERAL})")
class _:
    def s_expr(expr, env0, _):
        [str_lit] = expr.children
        return (T_String, env0)

# ------------------------------------------------------------------------------
# Going from a String value to some other type of value:

@P(r"{EXPR} : a List whose elements are the code units that are the elements of {var}")
@P(r"{EXPR} : a List consisting of the sequence of code units that are the elements of {var}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_String)
        return (ListType(T_code_unit_), env0)

@P(r"{EXPR} : the result of interpreting each of {var}'s 16-bit elements as a Unicode BMP code point. UTF-16 decoding is not applied to the elements")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_String)
        return (T_Unicode_code_points_, env0)

@P(r"{EXPR} : the sequence of code points resulting from interpreting each of the 16-bit elements of {var} as a Unicode BMP code point. UTF-16 decoding is not applied to the elements")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_String)
        return (T_Unicode_code_points_, env0)

@P(r"{EXPR} : the integer value that is represented by {var} in radix-{var} notation, using the letters <b>A</b> through <b>Z</b> and <b>a</b> through <b>z</b> for digits with values 10 through 35")
class _:
    def s_expr(expr, env0, _):
        [zvar, rvar] = expr.children
        env0.assert_expr_is_of_type(zvar, T_String)
        env0.assert_expr_is_of_type(rvar, T_MathInteger_)
        return (T_MathInteger_, env0)

# ------------------------------------------------------------------------------
# Comparing a String value to a nonterminal:

    # for 19.2.4 parseFloat
@P(r"{EXPR} : the longest prefix of {var} that satisfies the syntax of a {nonterminal}, which might be {var} itself. If there is no such prefix, return {NUMBER_LITERAL}")
class _:
    def s_expr(expr, env0, _):
        [var1, nont, var2, lit] = expr.children
        assert same_source_text(var1, var2)
        env0.assert_expr_is_of_type(var1, T_Unicode_code_points_)
        proc_add_return(env0, T_Number, lit)
        return (T_Unicode_code_points_, env0)

# ==============================================================================
#@ 6.1.5 The Symbol Type

@P('{VAL_DESC} : a Symbol')
class _:
    s_tb = T_Symbol

# ----

@P(r"{LITERAL} : {atat_word}")
class _:
    def s_expr(expr, env0, _):
        return (T_Symbol, env0)

#> Each Symbol value immutably holds
#> an associated value called [[Description]]
#> that is either *undefined* or a String value.

@P(r"{EXPR} : a new Symbol whose {DSBN} is {var}")
class _:
    def s_expr(expr, env0, _):
        [dsbn, var] = expr.children
        assert dsbn.source_text() == '[[Description]]'
        env0.assert_expr_is_of_type(var, T_String | T_Undefined)
        return (T_Symbol, env0)

@P(r"{EXPR} : {var}'s {DSBN} value")
class _:
    def s_expr(expr, env0, _):
        [var, dsbn] = expr.children
        env0.assert_expr_is_of_type(var, T_Symbol)
        assert dsbn.source_text() == '[[Description]]'
        return (T_String | T_Undefined, env0)

# ==============================================================================
#@ 6.1.6 Numeric Types

# ==============================================================================
#@ 6.1.6.1 The Number Type

@P('{VAL_DESC} : a Number')
class _:
    s_tb = T_Number

@P(r"{CONDITION_1} : {var} is finite")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        (t, env1) = tc_expr(var, env0); assert env1 is env0
        if t.is_a_subtype_of_or_equal_to(T_Number):
            return env1.with_type_test(var, 'is a', T_FiniteNumber_, asserting)
        elif t.is_a_subtype_of_or_equal_to(T_ExtendedMathReal_):
            return env1.with_type_test(var, 'is a', T_MathReal_, asserting)
        else:
            assert 0

@P(r"{CONDITION_1} : {var} and {var} are both finite")
class _:
    def s_cond(cond, env0, asserting):
        [a, b] = cond.children
        (a_t_env, a_f_env) = env0.with_type_test(a, 'is a', T_FiniteNumber_, asserting)
        (b_t_env, b_f_env) = env0.with_type_test(b, 'is a', T_FiniteNumber_, asserting)
        return (
            env_and(a_t_env, b_t_env),
            env_or(a_f_env, b_f_env)
        )

@P(r"{CONDITION_1} : {var} and {var} are finite and non-zero")
class _:
    def s_cond(cond, env0, asserting):
        [avar, bvar] = cond.children
        env0.assert_expr_is_of_type(avar, T_Number)
        env0.assert_expr_is_of_type(bvar, T_Number)
        return (
            env0
                .with_expr_type_narrowed(avar, T_FiniteNumber_)
                .with_expr_type_narrowed(bvar, T_FiniteNumber_),
            env0
        )

@P(r"{CONDITION_1} : {var} is not finite")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        (t, env1) = tc_expr(var, env0); assert env1 is env0
        if t.is_a_subtype_of_or_equal_to(T_Number | T_BigInt):
            return env1.with_type_test(var, 'isnt a', T_FiniteNumber_, asserting)
        elif t.is_a_subtype_of_or_equal_to(T_ExtendedMathReal_):
            return env1.with_type_test(var, 'isnt a', T_MathReal_, asserting)
        else:
            assert 0

@P(r"{CONDITION_1} : {var} is finite and is neither {NUMBER_LITERAL} nor {NUMBER_LITERAL}")
class _:
    def s_cond(cond, env0, asserting):
        [var, lita, litb] = cond.children
        env1 = env0.ensure_expr_is_of_type(var, T_FiniteNumber_)
        env1.assert_expr_is_of_type(lita, T_FiniteNumber_)
        env1.assert_expr_is_of_type(litb, T_FiniteNumber_)
        return (env1, env1)

@P(r"{NUMBER_LITERAL} : {starred_neg_infinity_lit}{h_sub_fancy_f}")
class _:
    s_tb = T_NegInfinityNumber_

    def s_expr(expr, env0, _):
        return (T_NegInfinityNumber_, env0)

@P(r"{NUMBER_LITERAL} : {starred_pos_infinity_lit}{h_sub_fancy_f}")
class _:
    s_tb = T_PosInfinityNumber_

    def s_expr(expr, env0, _):
        return (T_PosInfinityNumber_, env0)

@P(r"{NUMBER_LITERAL} : {starred_nan_lit}")
@P(r'{NUMBER_LITERAL} : the *NaN* Number value')
class _:
    s_tb = T_NaN_Number_

    def s_expr(expr, env0, _):
        return (T_NaN_Number_, env0)

@P(r"{NUMBER_LITERAL} : *0.5*{h_sub_fancy_f}")
@P(r"{NUMBER_LITERAL} : *-0.5*{h_sub_fancy_f}")
class _:
    def s_expr(expr, env0, _):
        return (T_NonIntegralFiniteNumber_, env0)

@P(r"{NUMBER_LITERAL} : {starred_int_lit}{h_sub_fancy_f}")
class _:
    s_tb = a_subset_of(T_IntegralNumber_)

    def s_expr(expr, env0, _):
        [_, _] = expr.children
        return (T_IntegralNumber_, env0)

@P(r'{EXPR} : the Number value that corresponds to {var}')
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_IEEE_binary32_ | T_IEEE_binary64_ | T_MathInteger_)
        return (T_Number, env1)

@P(r"{EX} : the Number value for {EX}")
class _:
    def s_expr(expr, env0, _):
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

@P(r"{EXPR} : the result of negating {var}; that is, compute a Number with the same magnitude but opposite sign")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_Number)
        return (T_Number, env0)

@P(r"{EXPR} : the smallest (closest to -∞) integral Number value that is not less than {var}")
@P(r"{EXPR} : the greatest (closest to +∞) integral Number value that is not greater than {var}")
@P(r"{EXPR} : the integral Number closest to {var}, preferring the Number closer to +∞ in the case of a tie")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_Number)
        return (T_Number, env0)

@P('{EXPR} : the largest integral Number {DEFVAR} (closest to +\u221e) such that {CONDITION_1}')
class _:
    def s_expr(expr, env0, _):
        [defvar, cond] = expr.children
        env1 = env0.plus_new_entry(defvar, T_IntegralNumber_)
        (t_env, _) = tc_cond(cond, env1)
        return (T_IntegralNumber_, t_env)

@P(r"{EXPR} : the integral Number nearest {var} in the direction of *+0*{h_sub_fancy_f}")
class _:
    def s_expr(expr, env0, _):
        [var, _] = expr.children
        env0.assert_expr_is_of_type(var, T_Number)
        return (T_Number, env0)

@P(r"{EXPR} : an implementation-approximated Number value representing {EXPR}")
class _:
    def s_expr(expr, env0, _):
        [ex] = expr.children
        env0.assert_expr_is_of_type(ex, T_MathReal_)
        return (T_Number, env0)

@P(r"{EXPR} : the result of converting {var} to IEEE 754-2019 binary32 format using roundTiesToEven mode")
@P(r"{EXPR} : the result of converting {var} to IEEE 754-2019 binary64 format")
@P(r"{EXPR} : the ECMAScript Number value corresponding to {var}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_Number)
        # XXX The intermediates are not really T_Number
        return (T_Number, env0)

@P(r'{EXPR} : a List whose elements are the 4 bytes that are the result of converting {var} to IEEE 754-2019 binary32 format using roundTiesToEven mode. The bytes are arranged in little endian order. If {var} is *NaN*, {var} may be set to any implementation chosen IEEE 754-2019 binary32 format Not-a-Number encoding. An implementation must always choose the same encoding for each implementation distinguishable *NaN* value')
@P(r'{EXPR} : a List whose elements are the 8 bytes that are the IEEE 754-2019 binary64 format encoding of {var}. The bytes are arranged in little endian order. If {var} is *NaN*, {var} may be set to any implementation chosen IEEE 754-2019 binary64 format Not-a-Number encoding. An implementation must always choose the same encoding for each implementation distinguishable *NaN* value')
class _:
    def s_expr(expr, env0, _):
        var = expr.children[0]
        env1 = env0.ensure_expr_is_of_type(var, T_Number)
        return (ListType(T_MathInteger_), env1)

# Treating an integral Number like a bit-string:

@P(r"{EXPR} : the result of applying bitwise complement to {var}. The mathematical value of the result is exactly representable as a 32-bit two's complement bit string")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_IntegralNumber_)
        return (T_IntegralNumber_, env0)

@P(r"{EX} : the result of left shifting {var} by {var} bits. The mathematical value of the result is exactly representable as a 32-bit two's complement bit string")
@P(r"{EXPR} : the result of performing a sign-extending right shift of {var} by {var} bits. The most significant bit is propagated. The mathematical value of the result is exactly representable as a 32-bit two's complement bit string")
@P(r"{EXPR} : the result of performing a zero-filling right shift of {var} by {var} bits. Vacated bits are filled with zero. The mathematical value of the result is exactly representable as a 32-bit unsigned bit string")
class _:
    def s_expr(expr, env0, _):
        [avar, bvar] = expr.children
        env1 = env0.ensure_expr_is_of_type(avar, T_IntegralNumber_)
        env1.assert_expr_is_of_type(bvar, T_MathInteger_)
        return (T_IntegralNumber_, env1)

@P(r"{EXPR} : the number of leading zero bits in the unsigned 32-bit binary representation of {var}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_IntegralNumber_)
        return (T_MathNonNegativeInteger_, env0)

# ------------------------------------------------------------------------------

@P('{VAL_DESC} : an IEEE 754-2019 binary32 NaN value')
class _:
    s_tb = a_subset_of(T_IEEE_binary32_)

@P('{VAL_DESC} : an IEEE 754-2019 binary64 NaN value')
class _:
    s_tb = a_subset_of(T_IEEE_binary64_)

# ==============================================================================
#@ 6.1.6.2 The BigInt Type

@P('{VAL_DESC} : a BigInt')
class _:
    s_tb = T_BigInt

@P('{LIST_ELEMENTS_DESCRIPTION} : BigInts')
class _:
    s_tb = T_BigInt

@P('{LITERAL} : {BIGINT_LITERAL}')
class _:
    s_tb = a_subset_of(T_BigInt)
    s_expr = s_expr_pass_down

# ----

@P(r"{BIGINT_LITERAL} : {starred_int_lit}{h_sub_fancy_z}")
class _:
    def s_expr(expr, env0, _):
        [_, _] = expr.children
        return (T_BigInt, env0)

@P(r"{EXPR} : the BigInt value that represents {EX}")
class _:
    def s_expr(expr, env0, _):
        [ex] = expr.children
        env0.assert_expr_is_of_type(ex, T_MathReal_|T_BigInt)
        return (T_BigInt, env0)

@P(r"{EXPR} : the BigInt value that corresponds to {var}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_MathInteger_)
        return (T_BigInt, env0)

@P(r"{EX} : the BigInt value for {EX}")
class _:
    def s_expr(expr, env0, _):
        [ex] = expr.children
        env0.assert_expr_is_of_type(ex, T_MathInteger_)
        return (T_BigInt, env0)

@P(r"{EX} : the sum of {var} and {var}")
@P(r"{EX} : the product of {var} and {var}")
@P(r"{EX} : the difference {var} minus {var}")
class _:
    def s_expr(expr, env0, _):
        [x, y] = expr.children
        env0.assert_expr_is_of_type(x, T_BigInt)
        env0.assert_expr_is_of_type(y, T_BigInt)
        return (T_BigInt, env0)

@P(r"{EXPR} : the String value consisting of the representation of {var} using radix {var}")
class _:
    def s_expr(expr, env0, _):
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

@P('{VAL_DESC} : an Object')
class _:
    s_tb = T_Object

@P(r"{VAL_DESC} : an Object that is defined by either an {nonterminal} or an {nonterminal}")
class _:
    s_tb = a_subset_of(T_Object)

@P('{VAL_DESC} : an extensible object that does not have a {starred_str} own property')
class _:
    s_tb = a_subset_of(T_Object)

@P('{VAL_DESC} : a property key')
class _:
    s_tb = T_String | T_Symbol

@P('{LIST_ELEMENTS_DESCRIPTION} : Objects')
class _:
    s_tb = T_Object

@P('{LIST_ELEMENTS_DESCRIPTION} : either Objects or Symbols')
class _:
    s_tb = T_Object | T_Symbol

@P('{LIST_ELEMENTS_DESCRIPTION} : property keys')
class _:
    s_tb = T_String | T_Symbol

@P('{VAL_DESC} : an? {PROPERTY_KIND} property')
class _:
    def s_tb(val_desc, env):
        [kind] = val_desc.children
        t = {
            'accessor': T_accessor_property_,
            'data'    : T_data_property_,
        }[kind.source_text()]
        return t

@P(r'{CONDITION_1} : {var} does not have an own property with key {var}')
@P(r"{CONDITION_1} : {var} does not currently have a property {var}")
class _:
    def s_cond(cond, env0, asserting):
        [obj_var, key_var] = cond.children
        env0.assert_expr_is_of_type(obj_var, T_Object)
        env0.assert_expr_is_of_type(key_var, T_String | T_Symbol)
        return (env0, env0)

@P(r'''{CONDITION_1} : The mathematical value of {var}'s {starred_str} property is {EX}''')
class _:
    def s_cond(cond, env0, asserting):
        [var, prop_name, ex] = cond.children
        env0.assert_expr_is_of_type(var, T_Object)
        env0.assert_expr_is_of_type(ex, T_MathInteger_)
        return (env0, env0)

@P(r"{EACH_THING} : own property key {DEFVAR} of {var} such that {CONDITION}, in ascending numeric index order")
@P(r"{EACH_THING} : own property key {DEFVAR} of {var} such that {CONDITION}, in ascending chronological order of property creation")
@P(r"{EACH_THING} : own property key {DEFVAR} of {var} such that {CONDITION}, in descending numeric index order")
class _:
    def s_nv(each_thing, env0):
        [loop_var, obj_var, condition] = each_thing.children
        env0.assert_expr_is_of_type(obj_var, T_Object)
        env1 = env0.plus_new_entry(loop_var, T_String | T_Symbol)
        (tenv, fenv) = tc_cond(condition, env1)
        return tenv

@P(r'{COMMAND} : Create own properties of {var} corresponding to the definitions in {h_emu_xref}.')
class _:
    def s_nv(anode, env0):
        [var, emu_xref] = anode.children
        env0.assert_expr_is_of_type(var, T_Object)
        return env0

@P(r"{COMMAND} : Remove the own property with name {var} from {var}.")
class _:
    def s_nv(anode, env0):
        [name_var, obj_var] = anode.children
        env0.assert_expr_is_of_type(name_var, T_String | T_Symbol)
        env0.assert_expr_is_of_type(obj_var, T_Object)
        return env0

@P(r"{EXPR} : {var}'s own property whose key is {var}")
class _:
    def s_expr(expr, env0, _):
        [obj_var, key_var] = expr.children
        env0.assert_expr_is_of_type(obj_var, T_Object)
        env0.assert_expr_is_of_type(key_var, T_String | T_Symbol)
        return (T_property_, env0)

@P(r"{EXPR} : the String value of the property name")
class _:
    def s_expr(expr, env0, _):
        # property of the Global Object
        # todo: make that explicit
        [] = expr.children
        return (T_String, env0)

@P(r"{EXPR} : such an object created in a host-defined manner")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_Object, env0)

#> An <dfn>integer index</dfn>
#> is a String-valued property key
#> that is a canonical numeric string
#> and whose numeric value is either *+0*<sub>𝔽</sub> or a positive integral Number ≤ 𝔽(2<sup>53</sup> - 1).

@P('{VAL_DESC} : an integer index')
class _:
    s_tb = a_subset_of(T_String)

#> An <dfn>array index</dfn>
#> is an integer index whose numeric value _i_
#> is in the range <emu-eqn>*+0*<sub>𝔽</sub> ≤ _i_ &lt; 𝔽(2<sup>32</sup> - 1)</emu-eqn>.

@P('{VAL_DESC} : an array index')
class _:
    s_tb = a_subset_of(T_String)

# ==============================================================================
#@ 6.1.7.1 Property Attributes

@P(r"{COMMAND} : Create an own {PROPERTY_KIND} property named {var} of object {var} whose {dsb_word}, {dsb_word}, {dsb_word}, and {dsb_word} attributes are set to the value of the corresponding field in {var} if {var} has that field, or to the attribute's {h_emu_xref} otherwise.")
class _:
    def s_nv(anode, env0):
        [kind, name_var, obj_var, *dsbw_, desc_var, desc_var2, emu_xref] = anode.children
        assert desc_var.source_text() == desc_var2.source_text()
        env0.ensure_expr_is_of_type(name_var, T_String | T_Symbol)
        env0.assert_expr_is_of_type(obj_var, T_Object)
        env0.assert_expr_is_of_type(desc_var, T_Property_Descriptor)
        return env0

@P(r"{SMALL_COMMAND} : set the corresponding attribute of the property named {var} of object {var} to the value of the field")
class _:
    def s_nv(anode, env0):
        [name_var, obj_var] = anode.children
        env0.ensure_expr_is_of_type(name_var, T_String | T_Symbol)
        env0.assert_expr_is_of_type(obj_var, T_Object)
        return env0

@P(r"{COMMAND} : Replace the property named {var} of object {var} with an? {PROPERTY_KIND} property whose {dsb_word} and {dsb_word} attributes are set to {var} and {var}, respectively, and whose {dsb_word} and {dsb_word} attributes are set to the value of the corresponding field in {var} if {var} has that field, or to the attribute's {h_emu_xref} otherwise.")
class _:
    def s_nv(anode, env0):
        [name_var, obj_var, kind, dsbw1, dsbw2, field_var1, field_var2, dsbw3, dsbw4, desc_var, desc_var2, emu_xref] = anode.children
        assert desc_var.source_text() == desc_var2.source_text()
        env0.ensure_expr_is_of_type(name_var, T_String | T_Symbol)
        env0.assert_expr_is_of_type(obj_var, T_Object)
        env0.assert_expr_is_of_type(desc_var, T_Property_Descriptor)
        return env0

@P(r"{SETTABLE} : {var}'s {DSBN} attribute")
class _:
    def s_expr(expr, env0, _):
        [prop_var, dsbn] = expr.children
        dsbn_name = dsbn.source_text()
        if dsbn_name in ['[[Enumerable]]', '[[Configurable]]']:
            env0.assert_expr_is_of_type(prop_var, T_property_)
            result_type = T_Boolean
        elif dsbn_name in ['[[Value]]', '[[Writable]]']:
            env0.assert_expr_is_of_type(prop_var, T_data_property_)
            result_type = T_Tangible_ if dsbn_name == '[[Value]]' else T_Boolean
        elif dsbn_name in ['[[Get]]', '[[Set]]']:
            env0.assert_expr_is_of_type(prop_var, T_accessor_property_)
            result_type = T_Object | T_Undefined
        else:
            assert 0
        return (result_type, env0)

@P(r'{EXPR} : an Iterator object ({h_emu_xref}) whose `next` method iterates over all the String-valued keys of enumerable properties of {var}. The iterator object is never directly accessible to ECMAScript code. The mechanics and order of enumerating the properties is not specified but must conform to the rules specified below')
class _:
    def s_expr(expr, env0, _):
        [emu_xref, var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_Object)
        return (T_Iterator_object_, env1)

# ==============================================================================
#@ 6.1.7.2 Object Internal Methods and Internal Slots

#> The actual semantics of objects, in ECMAScript, are specified via
#> algorithms called <em>internal methods</em>.
#> Each object in an ECMAScript engine is associated with
#> a set of internal methods that defines its runtime behaviour

@P(r'{CONDITION_1} : {var} has an? {DSBN} internal method')
class _:
    def s_cond(cond, env0, asserting):
        [var, dsbn] = cond.children
        env1 = env0.ensure_expr_is_of_type(var, T_Object)
        dsbn_name = dsbn.source_text()
        if dsbn_name == '[[Call]]':
            # one of the few where the presence/absence of an internal method is a type-test?
            return env1.with_type_test(var, 'is a', T_function_object_, asserting)
        elif dsbn_name == '[[Construct]]':
            return env1.with_type_test(var, 'is a', T_constructor_object_, asserting)
        else:
            assert 0, dsbn_name

#> Internal slots correspond to internal state
#> that is associated with objects
#> and used by various ECMAScript specification algorithms.

@P('{VAL_DESC} : an internal slot name')
class _:
    s_tb = T_SlotName_

@P('{LIST_ELEMENTS_DESCRIPTION} : internal slot names')
class _:
    s_tb = T_SlotName_

@P('{LIST_ELEMENTS_DESCRIPTION} : names of internal slots')
class _:
    s_tb = T_SlotName_

@P(r"{EX} : {DSBN}")
class _:
    def s_expr(expr, env0, _):
        [dsbn] = expr.children
        return (T_SlotName_, env0)

@P('{VAL_DESC} : an Object that has a {dsb_word} internal slot')
class _:
    s_tb = a_subset_of(T_Object)

@P(r'{CONDITION_1} : {var} has an? {DSBN} internal slot')
@P(r'{CONDITION_1} : {var} also has a {DSBN} internal slot')
class _:
    def s_cond(cond, env0, asserting):
        [var, dsbn] = cond.children
        env1 = env0.ensure_expr_is_of_type(var, T_Object)
        # Whether or not it has that particular slot, it's still an Object.
        # XXX we could be more specific about the sub-kind of Object
        return (env1, env1)

@P(r"{CONDITION_1} : {var} has {DSBN} and {DSBN} internal slots")
class _:
    def s_cond(cond, env0, asserting):
        # XXX could be a type-test
        [var, *dsbn_] = cond.children
        env0.assert_expr_is_of_type(var, T_Object)
        return (env0, env0)

@P(r"{CONDITION_1} : {var} has an? {DSBN} or {DSBN} internal slot")
class _:
    def s_cond(cond, env0, asserting):
        [var, dsbna, dsbnb] = cond.children
        env0.assert_expr_is_of_type(var, T_Object)
        assert dsbna.source_text() == '[[StringData]]'
        assert dsbnb.source_text() == '[[NumberData]]'
        return (env0, env0)

@P(r"{CONDITION_1} : {var} has an? {DSBN} internal slot whose value is an Object")
class _:
    def s_cond(cond, env0, asserting):
        [var, dsbn] = cond.children
        env0.assert_expr_is_of_type(var, T_Object) # more specific?
        return (env0, env0)

@P(r'{CONDITION_1} : {var} does not have an? {DSBN} internal slot')
class _:
    def s_cond(cond, env0, asserting):
        [var, dsbn] = cond.children
        env1 = env0.ensure_expr_is_of_type(var, T_Object)
        # Whether or not it has that particular slot, it's still an Object.
        # XXX The particular DSBN could have a (sub-)type-constraining effect
        return (env1, env1)

@P(r"{CONDITION_1} : {var} does not have an? {var} internal slot")
class _:
    def s_cond(cond, env0, asserting):
        [obj_var, slotname_var] = cond.children
        env0.assert_expr_is_of_type(obj_var, T_Object)
        env0.assert_expr_is_of_type(slotname_var, T_SlotName_)
        return (env0, env0)

@P(r"{CONDITION_1} : {var} does not have either a {DSBN} or an {DSBN} internal slot")
class _:
    def s_cond(cond, env0, asserting):
        [var, dsbna, dsbnb] = cond.children
        env0.assert_expr_is_of_type(var, T_Object)
        return (env0, env0)

@P(r"{CONDITION_1} : {var} has all of the internal slots of a For-In Iterator Instance ({h_emu_xref})")
class _:
    def s_cond(cond, env0, asserting):
        [var, emu_xref] = cond.children
        env0.assert_expr_is_of_type(var, T_Object)
        return (env0, env0)

    # explicit-exotics:
@P(r"{EX} : the internal slots listed in {h_emu_xref}")
class _:
    def s_expr(expr, env0, _):
        # XXX really, the *names* of the internal slots...
        return (ListType(T_SlotName_), env0)

#> All objects have an internal slot named [[PrivateElements]],
#> which is a List of PrivateElements.
#> This List represents the values of
#> the private fields, methods, and accessors for the object.
#> Initially, it is an empty List.

set_up_internal_thing('slot', '[[PrivateElements]]', ListType(T_PrivateElement))

#> Internal methods and internal slots are identified within this specification
#> using names enclosed in double square brackets [[ ]].

#> <emu-xref href="#table-essential-internal-methods"></emu-xref>
#> summarizes the <em>essential internal methods</em>
#> used by this specification
#> that are applicable to all objects created or manipulated by ECMAScript code.
#> Every object must have algorithms for all of the essential internal methods.
#> However, all objects do not necessarily use the same algorithms for those methods.

@P(r"{COMMAND} : Set {var}'s essential internal methods to the definitions specified in {h_emu_xref}.")
@P(r"{COMMAND} : Set {var}'s essential internal methods to the default ordinary object definitions specified in {h_emu_xref}.")
class _:
    def s_nv(anode, env0):
        [var, emu_xref] = anode.children
        env1 = env0.ensure_expr_is_of_type(var, T_Object)
        return env1

@P(r"{COMMAND} : Set {var}'s essential internal methods, except for {DSBN} and {DSBN}, to the definitions specified in {h_emu_xref}.")
class _:
    def s_nv(anode, env0):
        [var, _, _, emu_xref] = anode.children
        assert emu_xref.source_text() == '<emu-xref href="#sec-proxy-object-internal-methods-and-internal-slots"></emu-xref>'
        return env0.with_expr_type_narrowed(var, T_Proxy_exotic_object_)

    # explicit-exotics:
@P(r"{CONDITION_1} : the caller will not be overriding both {var}'s {DSBN} and {DSBN} essential internal methods")
@P(r"{CONDITION_1} : the caller will not be overriding all of {var}'s {DSBN}, {DSBN}, and {DSBN} essential internal methods")
class _:
    def s_cond(cond, env0, asserting):
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

@P('{VAL_DESC} : an ordinary object')
class _:
    s_tb = a_subset_of(T_Object)

@P('{VAL_DESC} : an ordinary, extensible object with no non-configurable properties')
class _:
    s_tb = a_subset_of(T_Object)

@P('{VAL_DESC} : an extensible ordinary object with no own properties')
class _:
    s_tb = a_subset_of(T_Object)

@P(r"{CONDITION_1} : {DOTTING} is not the ordinary object internal method defined in {h_emu_xref}")
class _:
    def s_cond(cond, env0, asserting):
        [dotting, emu_xref] = cond.children
        env0.assert_expr_is_of_type(dotting, T_proc_)
        return (env0, env0)

#> An <dfn>exotic object</dfn> is an object that is not an ordinary object.

#> A <dfn>function object</dfn> is an object that supports the [[Call]] internal method.
#> A <dfn>constructor</dfn> is an object that supports the [[Construct]] internal method.

@P('{VAL_DESC} : a function object')
class _:
    s_tb = T_function_object_

@P('{VAL_DESC} : a constructor')
class _:
    s_tb = T_constructor_object_

@P('{VAL_DESC} : a callable Object')
class _:
    s_tb = T_function_object_

# ------

# Creating objects:

@P(r'{EXPR} : a newly created object with an internal slot for each name in {var}')
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_SlotName_))
        return (T_Object, env1)

@P(r'{EXPR} : a new built-in function object that, when called, performs the action described by {var} using the provided arguments as the values of the corresponding parameters specified by {var}. The new function object has internal slots whose names are the elements of {var}, and an {DSBN} internal slot')
class _:
    def s_expr(expr, env0, _):
        [var1, var2, var3, dsbn] = expr.children
        env1 = env0.ensure_expr_is_of_type(var1, T_proc_ | T_alg_steps)
        # env1 = env0.ensure_expr_is_of_type(var2, )
        return (T_function_object_, env1)

@P(r"{EXPR} : a new {cap_word} object whose {dsb_word} internal slot is set to {var}. See {h_emu_xref} for a description of {cap_word} objects")
class _:
    def s_expr(expr, env0, _):
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

@P(r"{LITERAL} : {percent_word}")
class _:
    def s_expr(expr, env0, _):
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

@P(r"{EXPR} : the intrinsic function {percent_word}")
class _:
    def s_expr(expr, env0, _):
        [percent_word] = expr.children
        return (T_function_object_, env0)

@P(r"{EXPR} : {var}'s intrinsic object named {var}")
class _:
    def s_expr(expr, env0, _):
        [r_var, n_var] = expr.children
        env0.assert_expr_is_of_type(r_var, T_Realm_Record)
        env0.assert_expr_is_of_type(n_var, T_String)
        return (T_Object, env0)

    # 10.1.{13,14}
@P(r"{CONDITION_1} : {var} is this specification's name of an intrinsic object. The corresponding object must be an intrinsic that is intended to be used as the {DSBN} value of an object")
class _:
    def s_cond(cond, env0, asserting):
        [var, dsbn] = cond.children
        env0.assert_expr_is_of_type(var, T_String)
        return (env0, env0)

# ==============================================================================
#@ 6.2 ECMAScript Specification Types

# ==============================================================================
#@ 6.2.2 The List and Record Specification Types

# ------------------------------------------------------------------------------
# List:

@P('{VAL_DESC} : a possibly empty List')
class _:
    s_tb = T_List

@P('{VAL_DESC} : a List of {LIST_ELEMENTS_DESCRIPTION}')
class _:
    def s_tb(val_desc, env):
        [led] = val_desc.children
        (sub_t, sup_t) = type_bracket_for(led, env)
        return (ListType(sub_t), ListType(sup_t))

@P('{VAL_DESC} : a List of {LIST_ELEMENTS_DESCRIPTION} with length equal to {EX}')
class _:
    def s_tb(val_desc, env):
        [led, ex] = val_desc.children
        env.assert_expr_is_of_type(ex, T_MathInteger_)
        (led_sub_t, led_sup_t) = type_bracket_for(led, env)
        return a_subset_of(ListType(led_sup_t))
        # inexact because of length restriction

@P('{VAL_DESC} : a non-empty List of {LIST_ELEMENTS_DESCRIPTION}')
class _:
    def s_tb(val_desc, env):
        [led] = val_desc.children
        (led_sub_t, led_sup_t) = type_bracket_for(led, env)
        return a_subset_of(ListType(led_sup_t))
        # inexact because of 'non-empty'

@P('{VAL_DESC} : a possibly empty List, each of whose elements is a String or *undefined*')
class _:
    s_tb = ListType(T_String | T_Undefined)

# ------------------------------------------------------------------------------
# make a List:

@P(r"{EX} : « »")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (ListType(T_0), env0)

@P(r"{EX} : « {EXLIST} »")
class _:
    def s_expr(expr, env0, _):
        [exlist] = expr.children
        env1 = env0
        ex_types = set()
        for ex in exes_in_exlist(exlist):
            (ex_type, env1) = tc_expr(ex, env1)
            ex_types.add(ex_type)
        element_type = union_of_types(ex_types)
        list_type = ListType(element_type)
        return (list_type, env1)

@P(r'{EXPR} : a new empty List')
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (ListType(T_0), env0)

@P(r"{EXPR} : a List whose sole element is {EX}")
class _:
    def s_expr(expr, env0, _):
        [element_expr] = expr.children
        (element_type, env1) = tc_expr(element_expr, env0); assert env1.equals(env0)
        return (ListType(element_type), env0)

@P(r"{EXPR} : a copy of the List {var}")
@P(r"{EXPR} : a List whose elements are the elements of {var}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        t = env0.assert_expr_is_of_type(var, T_List)
        return (t, env0)

@P(r"{EXPR} : the list-concatenation of {EX} and {EX}")
class _:
    def s_expr(expr, env0, _):
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

@P(r"{EXPR} : the list-concatenation of {EX}, {EX}, and {EX}")
class _:
    def s_expr(expr, env0, _):
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

@P(r'{EXPR} : a List whose elements are the elements of {var} ordered as if an Array of the same values had been sorted using {percent_word} using {LITERAL} as {var}')
class _:
    def s_expr(expr, env0, _):
        [var, _, _, _] = expr.children
        (t, env1) = tc_expr(var, env0); assert env1 is env0
        assert t.is_a_subtype_of_or_equal_to(T_List)
        return (t, env0)

@P(r'{EXPR} : a List whose elements are the first {var} elements of {EX}')
class _:
    def s_expr(expr, env0, _):
        [nvar, listvar] = expr.children
        env0.assert_expr_is_of_type(nvar, T_MathNonNegativeInteger_)
        (t, env1) = tc_expr(listvar, env0); assert env1 is env0
        assert t.is_a_subtype_of_or_equal_to(T_List)
        return (t, env0)

@P(r"{EX} : {EX} occurrences of {code_unit_lit}")
class _:
    def s_expr(expr, env0, _):
        [ex, cu_lit] = expr.children
        env1 = env0.ensure_expr_is_of_type(ex, T_MathInteger_)
        env0.assert_expr_is_of_type(cu_lit, T_code_unit_)
        return (ListType(T_code_unit_), env1)

@P(r"{EXPR} : the List of {nonterminal} items in {PROD_REF}, in source text order")
class _:
    def s_expr(expr, env0, _):
        [nont, prod_ref] = expr.children
        return (ListType(T_Parse_Node), env0)

@P(r"{EXPR} : a List of {EX} {LITERAL} values, indexed 1 through {EX}")
class _:
    def s_expr(expr, env0, _):
        [var, literal, var2] = expr.children
        assert var.source_text() == var2.source_text()
        env0.assert_expr_is_of_type(var, T_MathInteger_)
        (lit_t, env1) = tc_expr(literal, env0); assert env1 is env0
        return (ListType(lit_t), env1)

# ------------------------------------------------------------------------------
# modify a List:

@P(r"{COMMAND} : Append {EX} to the end of {EX}.")
@P(r"{COMMAND} : Append {EX} to {EX}.")
@P(r"{COMMAND} : Insert {var} as the first element of {var}.")
@P(r"{COMMAND} : Prepend {var} to {var}.")
@P(r"{SMALL_COMMAND} : append {EX} to {SETTABLE}")
class _:
    def s_nv(anode, env0):
        [value_ex, list_ex] = anode.children
        return env0.ensure_A_can_be_element_of_list_B(value_ex, list_ex)

@P(r"{COMMAND} : Append to {var} the elements of {var}.")
class _:
    def s_nv(anode, env0):
        [lista, listb] = anode.children
        env0.assert_expr_is_of_type(lista, ListType(T_SlotName_))
        env0.assert_expr_is_of_type(listb, ListType(T_SlotName_))
        return env0

@P(r"{COMMAND} : Remove {var} from {var}.")
@P(r"{COMMAND} : Remove {var} from {DOTTING}.")
class _:
    def s_nv(anode, env0):
        [item_var, list_ex] = anode.children
        list_type = env0.assert_expr_is_of_type(list_ex, T_List)
        env0.assert_expr_is_of_type(item_var, list_type.element_type)
        return env0

@P(r"{COMMAND} : Remove the first element from {SETTABLE}.")
class _:
    def s_nv(anode, env0):
        [var] = anode.children
        env0.assert_expr_is_of_type(var, T_List)
        return env0

@P(r"{COMMAND} : Remove the first {var} elements of {SETTABLE}.")
class _:
    def s_nv(anode, env0):
        [nvar, listvar] = anode.children
        env0.assert_expr_is_of_type(nvar, T_MathNonNegativeInteger_)
        env0.assert_expr_is_of_type(listvar, T_List)
        return env0

@P(r"{COMMAND} : Remove the last element of {SETTABLE}.")
class _:
    def s_nv(anode, env0):
        [settable] = anode.children
        env0.assert_expr_is_of_type(settable, T_List)
        return env0

@P(r"{COMMAND} : Replace {var} in {var} with {var}.")
class _:
    def s_nv(anode, env0):
        [ex_var, list_var, rep_var] = anode.children
        env1 = env0.ensure_expr_is_of_type(list_var, ListType(T_PrivateElement))
        env1.assert_expr_is_of_type(ex_var, T_PrivateElement)
        env1.assert_expr_is_of_type(rep_var, T_PrivateElement)
        return env1

@P(r"{COMMAND} : Replace the element of {SETTABLE} whose value is {var} with an element whose value is {LITERAL}.")
class _:
    def s_nv(anode, env0):
        [list_var, elem_ex, lit] = anode.children
        env1 = env0.ensure_A_can_be_element_of_list_B(elem_ex, list_var)
        env2 = env1.ensure_A_can_be_element_of_list_B(lit, list_var)
        return env2

@P(r'{SMALL_COMMAND} : reverse the order of the elements of {var}')
class _:
    def s_nv(anode, env0):
        [var] = anode.children
        return env0.ensure_expr_is_of_type(var, T_List)

# ------------------------------------------------------------------------------
# iterate over a List:

@P(r"{EACH_THING} : element {DEFVAR} of {EX}")
@P(r"{EACH_THING} : element {DEFVAR} of {var}, in reverse List order")
class _:
    def s_nv(each_thing, env0):
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

@P(r'{CONDITION_1} : {EX} is empty')
@P(r"{CONDITION_1} : {EX} is not empty")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        # polymorphic
        env0.assert_expr_is_of_type(var, T_CharSet | T_List | T_String)
        # XXX For String, change spec to "is [not] the empty String" ?
        return (env0, env0)

@P(r"{CONDITION_1} : {var} is now an empty List")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_List)
        return (env0, env0)

@P(r"{CONDITION_1} : {var} has no elements")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_List)
        return (env0, env0)

@P(r"{CONDITION_1} : {var} has any elements")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_List)
        return (env0, env0)

@P(r"{CONDITION_1} : The length of {var} is {var}")
class _:
    def s_cond(cond, env0, asserting):
        [list_var, len_var] = cond.children
        env0.assert_expr_is_of_type(list_var, T_List)
        env0.assert_expr_is_of_type(len_var, T_MathNonNegativeInteger_)
        return (env0, env0)

@P(r"{EXPR} : the number of elements in the List {var}")
@P(r"{EX} : The number of elements in {var}")
@P(r"{EX} : the number of elements in {EX}")
@P(r"{NUM_COMPARAND} : the number of elements in the result of {NAMED_OPERATION_INVOCATION}")
@P(r"{NUM_COMPARAND} : the number of elements in {var}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_List)
        return (T_MathNonNegativeInteger_, env1)

@P(r"{CONDITION_1} : {var} has {EX} elements")
class _:
    def s_cond(cond, env0, asserting):
        [var, ex] = cond.children
        env0.assert_expr_is_of_type(var, T_List)
        env0.assert_expr_is_of_type(ex, T_MathNonNegativeInteger_)
        return (env0, env0)

@P(r"{CONDITION_1} : {var} contains any duplicate entries")
@P(r"{CONDITION_1} : {var} contains no duplicate entries")
@P(r"{CONDITION_1} : {var} has any duplicate entries")
@P(r"{CONDITION_1} : {var} has no duplicate entries")
@P(r"{CONDITION_1} : {NAMED_OPERATION_INVOCATION} contains any duplicate entries")
@P(r"{CONDITION_1} : {NAMED_OPERATION_INVOCATION} contains any duplicate elements")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_List)
        return (env0, env0)

@P(r"{CONDITION_1} : {var} contains a single {nonterminal}")
class _:
    def s_cond(cond, env0, asserting):
        [var, nonterminal] = cond.children
        env0.assert_expr_is_of_type(var, ListType(T_Parse_Node))
        return (env0, env0)

@P(r"{CONDITION_1} : {EX} contains {EX}")
@P(r"{CONDITION_1} : {EX} does not contain {EX}")
class _:
    def s_cond(cond, env0, asserting):
        [container_ex, value_var] = cond.children
        (container_type, container_env) = tc_expr(container_ex, env0)
        # polymorphic
        if container_type.is_a_subtype_of_or_equal_to(T_String):
            env1 = container_env.ensure_expr_is_of_type(value_var, T_String | T_code_unit_)
        elif container_type.is_a_subtype_of_or_equal_to(T_CharSet):
            env1 = container_env.ensure_expr_is_of_type(value_var, T_character_)
        elif container_type.is_a_subtype_of_or_equal_to(T_Relation):
            env1 = container_env.ensure_expr_is_of_type(value_var, T_event_pair_)
        else:
            env1 = env0.ensure_A_can_be_element_of_list_B(value_var, container_ex)
        return (env1, env1)

@P(r"{CONDITION_1} : {EX} contains {VAL_DESC} {DEFVAR} such that {CONDITION_1}")
class _:
    def s_cond(cond, env0, asserting):
        [list_ex, val_desc, new_var, stcond] = cond.children
        (list_t, env1) = tc_expr(list_ex, env0); assert env1 is env0
        assert list_t.is_a_subtype_of_or_equal_to(T_List)

        (sub_t, sup_t) = type_bracket_for(val_desc, env0)
        if list_t == T_List or list_t == ListType(T_0):
            pass
        else:
            assert sup_t.is_a_subtype_of_or_equal_to(list_t.element_type)

        env_for_cond = env0.plus_new_entry(new_var, sup_t)
        (cond_t_env, cond_f_env) = tc_cond(stcond, env_for_cond)
        return (cond_t_env, env0)


@P(r"{CONDITION_1} : {NAMED_OPERATION_INVOCATION} contains more than one occurrence of {starred_str}")
class _:
    def s_cond(cond, env0, asserting):
        [noi, ss] = cond.children
        env1 = env0.ensure_expr_is_of_type(noi, ListType(T_String))
        return (env1, env1)

@P(r"{CONDITION_1} : {NAMED_OPERATION_INVOCATION} contains any duplicate entries for {starred_str} and at least two of those entries were obtained from productions of the form {h_emu_grammar}")
class _:
    def s_cond(cond, env0, asserting):
        [noi, ss, emu_grammar] = cond.children
        env1 = env0.ensure_expr_is_of_type(noi, ListType(T_String))
        return (env1, env1)

@P(r"{CONDITION_1} : {var} does not include the element {LITERAL}")
class _:
    def s_cond(cond, env0, asserting):
        [list_var, item_lit] = cond.children
        env1 = env0.ensure_expr_is_of_type(list_var, ListType(T_String))
        env0.assert_expr_is_of_type(item_lit, T_String)
        return (env1, env1)

@P(r"{CONDITION_1} : {NAMED_OPERATION_INVOCATION} contains any {nonterminal}s")
class _:
    def s_cond(cond, env0, asserting):
        [noi, nont] = cond.children
        env0.assert_expr_is_of_type(noi, ListType(T_Parse_Node))
        return (env0, env0)

@P(r"{CONDITION_1} : there does not exist an element {DEFVAR} of {SETTABLE} such that {CONDITION_1}")
class _:
    def s_cond(cond, env0, asserting):
        [member_var, list_var, stcond] = cond.children
        env1 = env0.ensure_expr_is_of_type(list_var, ListType(T_String)) # over-specific
        env2 = env1.plus_new_entry(member_var, T_String)
        (t_env, f_env) = tc_cond(stcond, env2)
        return (env1, env1)

@P(r"{EXPR} : the first element of {SETTABLE}")
@P(r"{EXPR} : the last element of {var}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        list_type = env0.assert_expr_is_of_type(var, T_List)
        return (list_type.element_type, env0)

@P(r"{EXPR} : the sole element of {PP_NAMED_OPERATION_INVOCATION}")
@P(r"{EXPR} : the sole element of {var}")
class _:
    def s_expr(expr, env0, _):
        [noi] = expr.children
        list_type = env0.assert_expr_is_of_type(noi, T_List)
        return (list_type.element_type, env0)

@P(r"{EXPR} : {var}<sup>th</sup> element of {EX}")
class _:
    def s_expr(expr, env0, _):
        [subscript_var, list_ex] = expr.children
        env0.assert_expr_is_of_type(subscript_var, T_MathInteger_)
        list_type = env0.assert_expr_is_of_type(list_ex, T_List)
        return (list_type.element_type, env0)

@P(r"{SETTABLE} : {var}[{EX}]")
@P(r"{SETTABLE} : {DOTTING}[{EX}]")
class _:
    def s_expr(expr, env0, _):
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

@P(r"{CONDITION_1} : {var} and {var} have the same number of elements")
class _:
    def s_cond(cond, env0, asserting):
        [vara, varb] = cond.children
        env0.assert_expr_is_of_type(vara, T_List)
        env0.assert_expr_is_of_type(varb, T_List)
        return (env0, env0)

@P(r"{CONDITION_1} : {var} and {var} do not have the same number of elements")
class _:
    def s_cond(cond, env0, asserting):
        [vara, varb] = cond.children
        env0.assert_expr_is_of_type(vara, T_List)
        env0.assert_expr_is_of_type(varb, T_List)
        return (env0, env0)

@P(r"{CONDITION_1} : {var}, {var}, and {var} have the same number of elements")
class _:
    def s_cond(cond, env0, asserting):
        [vara, varb, varc] = cond.children
        env0.assert_expr_is_of_type(vara, T_List)
        env0.assert_expr_is_of_type(varb, T_List)
        env0.assert_expr_is_of_type(varc, T_List)
        return (env0, env0)

@P(r"{CONDITION_1} : any element of {NAMED_OPERATION_INVOCATION} also occurs in {NAMED_OPERATION_INVOCATION}")
class _:
    def s_cond(cond, env0, asserting):
        [noi1, noi2] = cond.children
        env0.assert_expr_is_of_type(noi1, T_List)
        env0.assert_expr_is_of_type(noi2, T_List)
        return (env0, env0)

@P(r"{CONDITION_1} : any element of {NAMED_OPERATION_INVOCATION} does not also occur in either {NAMED_OPERATION_INVOCATION}, or {NAMED_OPERATION_INVOCATION}")
class _:
    def s_cond(cond, env0, asserting):
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

@P(r"{EXPR} : a new Record")
class _:
    def s_expr(expr, env0, _):
        # Once, in CreateIntrinsics
        [] = expr.children
        return (T_Intrinsics_Record, env0)

#> A Record type value consists of one or more named fields.
#> The value of each field is an ECMAScript language value or specification value.
#> Field names are always enclosed in double brackets, for example [[Value]].

@P(r"{CONDITION_1} : {SETTABLE} has an? {DSBN} field")
class _:
    def s_cond(cond, env0, asserting):
        [settable, dsbn] = cond.children
        dsbn_name = dsbn.source_text()
        t = env0.assert_expr_is_of_type(settable, T_Record)
        if t.name == 'Environment Record' and dsbn_name == '[[NewTarget]]':
            add_pass_error(
                cond,
                "STA can't confirm that `%s` could have a %s field"
                % ( settable.source_text(), dsbn_name )
            )
            # We could confirm if we looked at the subtypes and what fields they have.
            return env0.with_type_test(settable, 'is a', [T_0, T_Function_Environment_Record], asserting)
        else:
            assert dsbn_name in fields_for_record_type_named_[t.name], (t.name, dsbn_name)
            return (env0, env0)

@P(r'{CONDITION_1} : {var} does not have an? {DSBN} field')
class _:
    def s_cond(cond, env0, asserting):
        [var, dsbn] = cond.children
        env1 = env0.ensure_expr_is_of_type(var, T_Record)
        # XXX We should check whether its type says it *could* have such a field.
        # XXX The particular DSBN could have a (sub-)type-constraining effect
        return (env1, env1)

@P(r"{CONDITION_1} : That Record's {dsb_word} is {EX}")
class _:
    def s_cond(cond, env0, asserting):
        [dsb_word, ex] = cond.children
        dsbn_name = dsb_word.source_text()
        # "That Record" is from prev step's "contains a Record"
        assert dsbn_name == '[[Module]]'
        field_type = T_Module_Record
        env0.assert_expr_is_of_type(ex, field_type)
        return (env0, env0)

@P('{VAL_DESC} : a Record with fields {dsb_word} ({VALUE_DESCRIPTION}) and {dsb_word} ({VALUE_DESCRIPTION})')
@P('{VAL_DESC} : a Record with fields {dsb_word} ({VALUE_DESCRIPTION}), {dsb_word} ({VALUE_DESCRIPTION}), and {dsb_word} ({VALUE_DESCRIPTION})')
@P('{LIST_ELEMENTS_DESCRIPTION} : Records with fields {dsb_word} ({VAL_DESC}) and {dsb_word} ({VAL_DESC})')
class _:
    def s_tb(val_desc, env):
        fields_info = []
        assert len(val_desc.children) % 2 == 0
        for i in range(0, len(val_desc.children), 2):
            field_dsb_word = val_desc.children[i]
            field_val_desc = val_desc.children[i+1]
            field_name = field_dsb_word.source_text()
            field_type = convert_nature_node_to_type(field_val_desc)
            fields_info.append( (field_name, field_type) )
        return RecordType('', tuple(fields_info))

@P(r"{SETTABLE} : the {DSBN} field of {EXPR}")
class _:
    def s_expr(expr, env0, _):
        [dsbn, ex] = expr.children
        dsbn_name = dsbn.source_text()
        if dsbn_name == '[[EventList]]':
            env0.assert_expr_is_of_type(ex, T_Agent_Events_Record)
            return (ListType(T_Event), env0)
        elif dsbn_name == '[[CandidateExecution]]':
            env0.assert_expr_is_of_type(ex, T_Agent_Record)
            return (T_Candidate_Execution_Record, env0)
        elif dsbn_name == '[[LittleEndian]]':
            env0.assert_expr_is_of_type(ex, T_Agent_Record)
            return (T_Boolean, env0)
        else:
            assert 0, expr

#> For notational convenience within this specification,
#> an object literal-like syntax can be used to express a Record value.

@P('{RECORD_CONSTRUCTOR} : {RECORD_CONSTRUCTOR_PREFIX} { {FIELDS} }')
class _:
    def s_expr(expr, env0, _):
        [record_constructor_prefix, fields] = expr.children
        constructor_prefix = record_constructor_prefix.source_text().replace('the ', '')

        if constructor_prefix in ['Record', 'Completion Record']:
            schema_name = '' if constructor_prefix == 'Record' else constructor_prefix
            env = env0
            fields_info = []
            for (field_name, field_ex) in get_field_items(fields):
                (field_type, env) = tc_expr(field_ex, env)
                fields_info.append( (field_name, field_type) )
            rt = RecordType(schema_name, tuple(fields_info))
            return (rt, env)

        else:
            if constructor_prefix in [
                'ReadModifyWriteSharedMemory',
                'ReadSharedMemory',
                'WriteSharedMemory',
            ]:
                record_type_name = constructor_prefix + ' Event'
            elif constructor_prefix in [
                'PromiseReaction',
                'PromiseCapability',
                'AsyncGeneratorRequest',
            ]:
                record_type_name = constructor_prefix + ' Record'
            elif constructor_prefix == 'PropertyDescriptor':
                record_type_name = 'Property Descriptor'
            elif constructor_prefix == 'a new ExportEntry Record':
                record_type_name = 'ExportEntry Record'
            elif constructor_prefix == 'a new Waiter Record':
                record_type_name = 'Waiter Record'
            else:
                record_type_name = constructor_prefix
            field_info = fields_for_record_type_named_[record_type_name]

        envs = []
        for (dsbn_name, ex) in get_field_items(fields):
            declared_field_type = field_info[dsbn_name]
            # If the constructor referred to an undeclared field, that would raise a KeyError
            env1 = env0.ensure_expr_is_of_type(ex, declared_field_type)
            envs.append(env1)
        env2 = envs_or(envs)

        # XXX: Should also ensure that each declared field is specified exactly once.

        return ( HierType(record_type_name), env2 )

#> In specification text and algorithms,
#> dot notation may be used to refer to a specific field of a Record value.
#> For example, if R is the record shown in the previous paragraph then
#> R.[[Field2]] is shorthand for “the field of R named [[Field2]]”.

@P(r'{DOTTING} : {var}.{DSBN}')
@P(r"{DOTTING} : {DOTTING}.{DSBN}")
class _:
    def s_expr(expr, env0, _):
        [lhs_var, dsbn] = expr.children
        lhs_text = lhs_var.source_text()
        dsbn_name = dsbn.source_text()
        (lhs_t, env1) = tc_expr(lhs_var, env0)

        # There are various things that can take a dot.

        (dottable_part_of_lhs_t, nondottable_part_of_lhs_t) = lhs_t.split_by(T_Record | T_Object | T_Symbol | T_Private_Name)

        msg_lines = []

        if dottable_part_of_lhs_t == T_0:
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
                dottable_part_of_lhs_t = T_ResolvedBinding_Record
            elif lhs_text == '_element_':
                dottable_part_of_lhs_t = T_PrivateElement
            else:
                assert 0, expr.source_text()

            msg_lines.append(f"which cannot take a dot")
            msg_lines.append(f"so changing its type to {dottable_part_of_lhs_t}")

        elif nondottable_part_of_lhs_t != T_0:
            msg_lines.append(f"of which {nondottable_part_of_lhs_t} cannot take a dot")
            msg_lines.append(f"so narrowing type to {dottable_part_of_lhs_t}")

        # --------------------------------------------

        final_lhs_t = T_0
        final_dotting_t = T_0

        for part_of_lhs_t in sorted(dottable_part_of_lhs_t.set_of_types()):

            if part_of_lhs_t == T_Symbol:
                if dsbn_name == '[[Description]]':
                    part_of_dotting_t = T_String | T_Undefined
                else:
                    part_of_dotting_t = None

            elif part_of_lhs_t == T_Private_Name:
                if dsbn_name == '[[Description]]':
                    part_of_dotting_t = T_String
                else:
                    part_of_dotting_t = None

            elif part_of_lhs_t.is_a_subtype_of_or_equal_to(T_Object):
                # _foo_.[[Bar]] references an object's internal method or internal slot.

                if dsbn_name in type_of_internal_thing_:
                    part_of_dotting_t = type_of_internal_thing_[dsbn_name]

                    # XXX We should require that part_of_lhs_t is allowed to have this internal thing.

                    # But for some subtypes of Object, we can give a narrower type for the slot
                    if part_of_lhs_t == T_SharedArrayBuffer_object_ and dsbn_name == '[[ArrayBufferData]]':
                        narrower_type = T_Shared_Data_Block
                        assert narrower_type.is_a_subtype_of_or_equal_to(part_of_dotting_t)
                        assert narrower_type != part_of_dotting_t
                        part_of_dotting_t = narrower_type

                    # or the the slot-name can give us a narrower type for the LHS
                    if part_of_lhs_t == T_Object and dsbn_name == '[[AsyncGeneratorState]]':
                        part_of_lhs_t = T_AsyncGenerator_object_
                        msg_lines.append(f"Within Object, only {part_of_lhs_t} supports .{dsbn_name}")

                else:
                    part_of_dotting_t = None

            elif part_of_lhs_t.is_a_subtype_of_or_equal_to(T_Record):
                # _foo_.[[Bar]] references a record's field
                if isinstance(part_of_lhs_t, HierType):
                    if part_of_lhs_t.name == 'Record':
                        msg_lines.append(f"so don't know about a {dsbn_name} field")
                        field_type = T_TBD

                    elif part_of_lhs_t.name == 'Intrinsics Record':
                        field_type = {
                            '[[%Array%]]'               : T_constructor_object_,
                            '[[%Function.prototype%]]'  : T_Object,
                            '[[%Object.prototype%]]'    : T_Object,
                            '[[%ThrowTypeError%]]'      : T_function_object_,
                        }[dsbn_name]

                    else:
                        assert part_of_lhs_t.name in fields_for_record_type_named_, part_of_lhs_t.name
                        fields_info = fields_for_record_type_named_[part_of_lhs_t.name]
                        if dsbn_name in fields_info:
                            field_type = fields_info[dsbn_name]
                        else:
                            msg_lines.append(f"{part_of_lhs_t} doesn't have a {dsbn_name} field")
                            # Probably you need to add something to
                            # fields_for_record_type_named_

                            field_type = T_TBD

                    part_of_dotting_t = field_type

                elif isinstance(part_of_lhs_t, RecordType):
                    field_type = part_of_lhs_t.type_of_field_named(dsbn_name)
                    part_of_dotting_t = field_type

                else:
                    assert 0, (expr.source_text(), part_of_lhs_t)

            else:
                assert 0, part_of_lhs_t

            if part_of_dotting_t is None:
                msg_lines.append(f"Dropping {part_of_lhs_t} from the lhs-type, because it doesn't support .{dsbn_name}")
            else:
                final_dotting_t |= part_of_dotting_t
                final_lhs_t |= part_of_lhs_t

        if final_lhs_t != lhs_t:
            env2 = env1.with_expr_type_replaced(lhs_var, final_lhs_t)
            if final_lhs_t != dottable_part_of_lhs_t:
                msg_lines.append(f"So final lhs-type is {final_lhs_t}")
        else:
            env2 = env1

        if msg_lines:
            msg_lines.insert(0, f"`{lhs_text}` has type {lhs_t},")
            msg = '\n    '.join(msg_lines)
            add_pass_error(lhs_var, msg)

        return (final_dotting_t, env2)

# ------------------------------------------------------------------------------
# List of Records

@P(r"{CONDITION_1} : All elements of {var} have their {dsb_word} field set to {LITERAL}, {dsb_word} field set to {LITERAL}, and {dsb_word} field set to {LITERAL}")
class _:
    def s_cond(cond, env0, asserting):
        [var, dsb1, lit1, dsb2, lit2, dsb3, lit3] = cond.children
        assert dsb1.source_text() == '[[AsyncEvaluation]]'
        assert dsb2.source_text() == '[[PendingAsyncDependencies]]'
        assert dsb3.source_text() == '[[EvaluationError]]'
        # could check that the lits have the right type.
        env0.assert_expr_is_of_type(var, ListType(T_Cyclic_Module_Record))
        return (env0, env0)

@P(r"{CONDITION_1} : {DOTTING} contains a Record {DEFVAR} such that {CONDITION_1}")
class _:
    def s_cond(cond, env0, asserting):
        [ex, var, stcond] = cond.children
        (ex_t, env1) = tc_expr(ex, env0); assert env1 is env0
        assert ex_t.is_a_subtype_of_or_equal_to(T_List)
        assert ex_t.element_type.is_a_subtype_of_or_equal_to(T_Record)
        env_for_cond = env0.plus_new_entry(var, ex_t.element_type)
        (cond_t_env, cond_f_env) = tc_cond(stcond, env_for_cond)
        return (cond_t_env, env0)

@P(r"{CONDITION_1} : {EX} contains a Record whose {dsb_word} is {var}")
@P(r"{CONDITION_1} : Exactly one element of {DOTTING} is a Record whose {dsb_word} is {var}")
class _:
    def s_cond(cond, env0, asserting):
        [list_ex, dsb_word, var] = cond.children
        dsbn_name = dsb_word.source_text()
        (list_type, env1) = tc_expr(list_ex, env0); assert env1 is env0
        assert isinstance(list_type, ListType)
        et = list_type.element_type
        assert isinstance(et, RecordType)
        assert et.schema_name == ''
        field_type = et.type_of_field_named(dsbn_name)
        env1.assert_expr_is_of_type(var, field_type)
        return (env0, env0)

@P(r"{EXPR} : the element of {EX} whose {DSBN} is {EX}")
@P(r"{EXPR} : the element of {EX} whose {DSBN} field is {var}")
class _:
    def s_expr(expr, env0, _):
        [list_ex, dsbn, val_ex] = expr.children
        dsbn_name = dsbn.source_text()
        (list_type, env1) = tc_expr(list_ex, env0); assert env1 is env0
        assert isinstance(list_type, ListType)
        et = list_type.element_type
        assert isinstance(et, HierType)
        fields = fields_for_record_type_named_[et.name]
        whose_type = fields[dsbn_name]
        env1.assert_expr_is_of_type(val_ex, whose_type)
        return (et, env1)

@P(r"{EXPR} : the Record in {DOTTING} whose {dsb_word} is {var}")
class _:
    def s_expr(expr, env0, _):
        [dotting, dsb_word, var] = expr.children
        dsbn_name = dsb_word.source_text()
        (list_type, env1) = tc_expr(dotting, env0); assert env1 is env0
        assert isinstance(list_type, ListType)
        et = list_type.element_type
        assert isinstance(et, RecordType)
        assert et.schema_name == ''
        whose_type = et.type_of_field_named(dsbn_name)
        env1.assert_expr_is_of_type(var, whose_type)
        return (et, env0)

# ==============================================================================
#@ 6.2.3 The Set and Relation Specification Types

#> Values of the Relation type
#> are Sets of ordered pairs of values from its value domain.

@P(r"{EXPR} : an empty Set")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_Set, env0)

@P(r"{PAIR} : ({EX}, {EX})")
class _:
    def s_expr(expr, env0, _):
        [a, b] = expr.children
        # over-specific:
        env0.assert_expr_is_of_type(a, T_Event)
        env0.assert_expr_is_of_type(b, T_Event)
        return (T_event_pair_, env0)

@P(r'{COMMAND} : Add {var} to {var}.')
@P(r"{SMALL_COMMAND} : add {var} to {var}")
class _:
    def s_nv(anode, env0):
        [item_var, collection_var] = anode.children
        (item_type, env1) = tc_expr(item_var, env0); assert env1 is env0
        (collection_type, env2) = tc_expr(collection_var, env0); assert env2 is env0
        if item_type.is_a_subtype_of_or_equal_to(T_Event) and collection_type == T_Set:
            pass
        else:
            assert 0
        return env0

@P(r"{CONDITION_1} : the pairs {PAIR} and {PAIR} are in {EX}")
@P(r"{CONDITION_1} : the pairs {PAIR} and {PAIR} are not in {EX}")
class _:
    def s_cond(cond, env0, asserting):
        [paira, pairb, ex] = cond.children
        env0.assert_expr_is_of_type(paira, T_event_pair_)
        env0.assert_expr_is_of_type(pairb, T_event_pair_)
        env0.assert_expr_is_of_type(ex, T_Relation)
        return (env0, env0)

@P(r"{CONDITION_1} : {EX} contains either {PAIR} or {PAIR}")
class _:
    def s_cond(cond, env0, asserting):
        [ex, paira, pairb] = cond.children
        env0.assert_expr_is_of_type(paira, T_event_pair_)
        env0.assert_expr_is_of_type(pairb, T_event_pair_)
        env0.assert_expr_is_of_type(ex, T_Relation)
        return (env0, env0)

@P(r"{CONDITION_1} : {var} is not in {PREFIX_PAREN}")
class _:
    def s_cond(cond, env0, asserting):
        [item_var, set_pp] = cond.children
        env0.assert_expr_is_of_type(set_pp, T_Set)
        env0.assert_expr_is_of_type(item_var, T_Event)
        return (env0, env0)

# ==============================================================================
#@ 6.2.4 The Completion Record Specification Type

T_Completion_Record = RecordType('Completion Record', ())
# We create this rather than creating HierType('Completion Record')
# in traverse_record_schema.

#> The following shorthand terms are sometimes used to refer to Completion Records.

@P('{VAL_DESC} : a Completion Record')
class _:
    s_tb = T_Completion_Record

#> <dfn>normal completion</dfn> refers to any Completion Record with a [[Type]] value of ~normal~.

T_normal_completion = CompletionType(T_tilde_normal_)

def NormalCompletionType(value_type):
    return RecordType(
        'Completion Record',
        (
            ('[[Type]]',  T_tilde_normal_),
            ('[[Value]]', value_type),
        )
    )

@P('{VAL_DESC} : a normal completion')
class _:
    s_tb = T_normal_completion

@P('{VAL_DESC} : a return completion')
class _:
    s_tb = T_return_completion

def ThrowCompletionType(error_type):
    return RecordType(
        'Completion Record',
        (
            ('[[Type]]', T_tilde_throw_),
            ('[[Value]]', error_type),
        )
    )

@P('{VAL_DESC} : a throw completion')
class _:
    s_tb = T_throw_completion

@P('{VAL_DESC} : an abrupt completion')
class _:
    s_tb = T_abrupt_completion

@P('{VAL_DESC} : any value except a Completion Record')
class _:
    s_tb = T_Tangible_ | T_Intangible_

@P('{VAL_DESC} : a normal completion containing {VALUE_DESCRIPTION}')
class _:
    def s_tb(vd, env):
        [child] = vd.children
        (sub_t, sup_t) = type_bracket_for(child, env)
        return (NormalCompletionType(sub_t), NormalCompletionType(sup_t))

@P(r"{CONDITION_1} : {var} is a normal completion with a value of {LITERAL}. The possible sources of this value are Await or, if the async function doesn't await anything, step {h_emu_xref} above")
class _:
    def s_cond(cond, env0, asserting):
        [var, literal, _] = cond.children
        env0.assert_expr_is_of_type(literal, T_tilde_unused_)
        return env0.with_type_test(var, 'is a', NormalCompletionType(T_tilde_unused_), asserting)

@P(r"{EXPR} : a new implementation-defined Completion Record")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_Completion_Record, env0)

# ---------

@P(r"{CONDITION_1} : The next step never returns an abrupt completion because {CONDITION_1}")
class _:
    def s_cond(cond, env0, asserting):
        [subcond] = cond.children
        return tc_cond(subcond, env0, asserting)

# ==============================================================================
#@ 6.2.5 The Reference Record Specification Type

@P('{VAL_DESC} : a Reference Record')
class _:
    s_tb = T_Reference_Record

@P('{VAL_DESC} : a Super Reference Record')
class _:
    s_tb = a_subset_of(T_Reference_Record)

# ==============================================================================
#@ 6.2.6 The Property Descriptor Specification Type

@P('{VAL_DESC} : a Property Descriptor')
class _:
    s_tb = T_Property_Descriptor

@P('{VAL_DESC} : a fully populated Property Descriptor')
class _:
    s_tb = a_subset_of(T_Property_Descriptor)

@P(r"{EXPR} : a newly created Property Descriptor with no fields")
@P(r"{EXPR} : a new Property Descriptor that initially has no fields")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_Property_Descriptor, env0)

@P(r"{EXPR} : the fully populated data Property Descriptor for the property, containing the specified attributes for the property. For properties listed in {h_emu_xref}, {h_emu_xref}, or {h_emu_xref} the value of the {DSBN} attribute is the corresponding intrinsic object from {var}")
class _:
    def s_expr(expr, env0, _):
        [emu_xref1, emu_xref2, emu_xref3, dsbn, var] = expr.children
        env0.assert_expr_is_of_type(var, T_Realm_Record)
        return (T_Property_Descriptor, env0)

@P(r"{CONDITION_1} : {var} does not have any fields")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_Property_Descriptor)
        return (env0, env0)

@P(r'{CONDITION_1} : {var} has attribute values { {DSBN}: *true*, {DSBN}: *true* }')
class _:
    def s_cond(cond, env0, asserting):
        [var, dsbn1, dsbn2] = cond.children
        env1 = env0.ensure_expr_is_of_type(var, T_Property_Descriptor)
        assert dsbn1.source_text() == '[[Writable]]'
        assert dsbn2.source_text() == '[[Enumerable]]'
        return (env1, env1)

@P(r"{EACH_THING} : field of {var}")
class _:
    def s_nv(each_thing, env0):
        [desc_var] = each_thing.children
        loop_var = None # todo: no loop variable!
        env0.assert_expr_is_of_type(desc_var, T_Property_Descriptor)
        return env0

# ==============================================================================
#@ 6.2.7 The Environment Record Specification Type

# (See 9.1 Environment Records)

# ==============================================================================
#@ 6.2.8 The Abstract Closure Specification Type

@P('{VAL_DESC} : an Abstract Closure with no parameters')
class _:
    s_tb = ProcType((), T_Completion_Record)

@P('{VAL_DESC} : an Abstract Closure with two parameters')
class _:
    s_tb = ProcType((T_Tangible_, T_Tangible_), NormalCompletionType(T_Number) | T_throw_completion)

@P('{VAL_DESC} : an Abstract Closure')
class _:
    s_tb = T_proc_

@P(r"{MULTILINE_EXPR} : a new {CLOSURE_KIND} with {CLOSURE_PARAMETERS} that captures {CLOSURE_CAPTURES} and performs the following {CLOSURE_STEPS} when called:{IND_COMMANDS}")
class _:
    def s_expr(expr, env0, _):
        [clo_kind, clo_parameters, clo_captures, _, commands] = expr.children
        clo_kind = clo_kind.source_text()

        # -----

        env_for_commands = Env(env0)

        parameter_names = [
            clo_param.source_text()
            for clo_param in clo_parameters.children
        ]
        expected_return_type = T_Top_
        # It would be nice if an abstract closure declared its return-type.
        returns_completion_records = False
        # TODO: Need to detect whether or not closure returns a completion.

        env_for_commands.parret = ParRet(parameter_names, expected_return_type, returns_completion_records)

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
            env_for_commands = env_for_commands.plus_new_entry(clo_capture_var, clo_capture_type, shadowing_outer_is_okay=True)

        env_for_commands.vars['*return*'] = T_0

        # -----

        defns = [(None, commands)]
        env_after_commands = tc_proc(None, defns, env_for_commands)
        t = ProcType(tuple(clo_param_types), env_after_commands.vars['*return*'])
        return (t, env0)

# ==============================================================================
#@ 6.2.9 Data Blocks

@P('{VAL_DESC} : a Data Block')
class _:
    s_tb = T_Data_Block

@P('{VAL_DESC} : a Shared Data Block')
class _:
    s_tb = T_Shared_Data_Block

@P('{VAL_DESC} : a Shared Data Block event')
class _:
    s_tb = T_Shared_Data_Block_Event

@P(r'{EXPR} : a new Data Block value consisting of {var} bytes. If it is impossible to create such a Data Block, throw a {ERROR_TYPE} exception')
class _:
    def s_expr(expr, env0, _):
        [var, error_type] = expr.children
        (t, env1) = tc_expr(var, env0)
        assert env1 is env0
        assert t.is_a_subtype_of_or_equal_to(T_MathInteger_)
        proc_add_return(env0, ThrowCompletionType(type_for_ERROR_TYPE(error_type)), error_type)
        return (T_Data_Block, env1)

@P(r'{EXPR} : a new Shared Data Block value consisting of {var} bytes. If it is impossible to create such a Shared Data Block, throw a {ERROR_TYPE} exception')
class _:
    def s_expr(expr, env0, _):
        [var, error_type] = expr.children
        (t, env1) = tc_expr(var, env0)
        assert env1 is env0
        assert t.is_a_subtype_of_or_equal_to(T_MathInteger_)
        proc_add_return(env0, ThrowCompletionType(type_for_ERROR_TYPE(error_type)), error_type)
        return (T_Shared_Data_Block, env1)

@P(r'{COMMAND} : Set all of the bytes of {var} to 0.')
class _:
    def s_nv(anode, env0):
        [var] = anode.children
        env1 = env0.ensure_expr_is_of_type(var, T_Data_Block)
        return env1

@P(r"{COMMAND} : Store the individual bytes of {var} into {var}, starting at {var}[{var}].")
class _:
    def s_nv(anode, env0):
        [var1, var2, var3, var4] = anode.children
        env0.assert_expr_is_of_type(var1, ListType(T_MathInteger_))
        env1 = env0.ensure_expr_is_of_type(var2, T_Data_Block)
        assert var3.children == var2.children
        env0.assert_expr_is_of_type(var4, T_MathInteger_)
        return env1

@P(r"{EXPR} : the number of bytes in {var}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_Data_Block | T_Shared_Data_Block)
        return (T_MathNonNegativeInteger_, env1)

@P(r"{EXPR} : a List of length {var} whose elements are the sequence of {var} bytes starting with {var}[{var}]")
class _:
    def s_expr(expr, env0, _):
        [var1, var2, var3, var4] = expr.children
        assert var1.children == var2.children
        env0.assert_expr_is_of_type(var1, T_MathInteger_)
        env1 = env0.ensure_expr_is_of_type(var3, T_Data_Block | T_Shared_Data_Block)
        env0.assert_expr_is_of_type(var4, T_MathInteger_)
        return (ListType(T_MathInteger_), env1)

@P(r"{EXPR} : a List whose elements are bytes from {var} at indices in {INTERVAL}")
class _:
    def s_expr(expr, env0, _):
        [data_var, interval] = expr.children
        env1 = env0.ensure_expr_is_of_type(data_var, T_Data_Block | T_Shared_Data_Block)
        env1.assert_expr_is_of_type(interval, T_MathNonNegativeInteger_)
        return (ListType(T_MathNonNegativeInteger_), env1)

@P(r"{EACH_THING} : index {DEFVAR} of {var}")
class _:
    def s_nv(each_thing, env0):
        [loop_var, collection_var] = each_thing.children
        env0.assert_expr_is_of_type(collection_var, T_Shared_Data_Block)
        return env0.plus_new_entry(loop_var, T_MathInteger_)

@P(r"{CONDITION_1} : {EX} and {EX} are valid byte offsets within the memory of {var}")
class _:
    def s_cond(cond, env0, asserting):
        [offset1, offset2, sdb] = cond.children
        env1 = env0.ensure_expr_is_of_type(offset1, T_MathInteger_)
        env1.assert_expr_is_of_type(offset2, T_MathInteger_)
        env1.assert_expr_is_of_type(sdb, T_Shared_Data_Block)
        return (env1, env1)

# ==============================================================================
#@ 6.2.10 The PrivateElement Specification Type

@P('{VAL_DESC} : a PrivateElement')
class _:
    s_tb = T_PrivateElement

@P('{LIST_ELEMENTS_DESCRIPTION} : PrivateElements')
class _:
    s_tb = T_PrivateElement

# ==============================================================================
#@ 6.2.11 The ClassFieldDefinition Record Specification Type

@P('{VAL_DESC} : a ClassFieldDefinition Record')
class _:
    s_tb = T_ClassFieldDefinition_Record

@P('{LIST_ELEMENTS_DESCRIPTION} : ClassFieldDefinition Records')
class _:
    s_tb = T_ClassFieldDefinition_Record

# ==============================================================================
#@ 6.2.12 Private Names

@P('{VAL_DESC} : a Private Name')
class _:
    s_tb = T_Private_Name

@P('{LIST_ELEMENTS_DESCRIPTION} : Private Names')
class _:
    s_tb = T_Private_Name

@P('{VAL_DESC} : a property key or Private Name')
class _:
    s_tb = T_String | T_Symbol | T_Private_Name

@P(r"{CONDITION_1} : {EX} contains a Private Name whose {dsb_word} is {var}")
class _:
    def s_cond(cond, env0, asserting):
        [ex, dsb_word, var] = cond.children
        env0.assert_expr_is_of_type(ex, ListType(T_Private_Name))
        assert dsb_word.source_text() == '[[Description]]'
        env0.assert_expr_is_of_type(var, T_String)
        return (env0, env0)

@P(r"{CONDITION_1} : Exactly one element of {var} is a Private Name whose {dsb_word} is {var}")
class _:
    def s_cond(cond, env0, asserting):
        [list_var, dsb_word, var] = cond.children
        env0.assert_expr_is_of_type(list_var, ListType(T_Private_Name))
        assert dsb_word.source_text() == '[[Description]]'
        env0.assert_expr_is_of_type(var, T_String)
        return (env0, env0)

@P(r"{EXPR} : a new Private Name whose {dsb_word} is {var}")
class _:
    def s_expr(expr, env0, _):
        [dsb_word, var] = expr.children
        assert dsb_word.source_text() == '[[Description]]'
        env0.assert_expr_is_of_type(var, T_String)
        return (T_Private_Name, env0)

@P(r"{EXPR} : the Private Name in {var} whose {dsb_word} is {var}")
class _:
    def s_expr(expr, env0, _):
        [list_var, dsb_word, var] = expr.children
        env0.assert_expr_is_of_type(list_var, ListType(T_Private_Name))
        assert dsb_word.source_text() == '[[Description]]'
        env0.assert_expr_is_of_type(var, T_String)
        return (T_Private_Name, env0)

# ==============================================================================
#@ 6.2.13 The ClassStaticBlockDefinition Record Specification Type

@P('{VAL_DESC} : a ClassStaticBlockDefinition Record')
class _:
    s_tb = T_ClassStaticBlockDefinition_Record

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 7 Abstract Operations

# ==============================================================================
#@ 7.1.13 ToBigInt

@P(r"{EXPR} : the value that {var} corresponds to in {h_emu_xref}")
class _:
    def s_expr(expr, env0, _):
        [var, xref] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_Primitive)
        assert xref.source_text() == '<emu-xref href="#table-tobigint"></emu-xref>'
        return (T_BigInt | ThrowCompletionType(T_TypeError) | ThrowCompletionType(T_SyntaxError), env1)

# ==============================================================================
#@ 7.4.1 Iterator Records

@P('{VAL_DESC} : an Iterator Record')
class _:
    s_tb = T_Iterator_Record

# ==============================================================================
#@ 7.4.9 IfAbruptCloseIterator

@P(r"{COMMAND} : IfAbruptCloseIterator({var}, {var}).")
class _:
    def s_nv(anode, env0):
        [vara, varb] = anode.children
        ta = env0.assert_expr_is_of_type(vara, T_Completion_Record)
        env0.assert_expr_is_of_type(varb, T_Iterator_Record)

        (normal_part_of_ta, abrupt_part_of_ta) = ta.split_by(T_normal_completion)

        if abrupt_part_of_ta == T_0:
            add_pass_error(
                vara,
                f"ST of {vara.source_text()} is {ta}\n    which can't be abrupt, so using 'IfAbruptCloseIterator' is a bit odd"
            )
        else:
            proc_add_return(env0, abrupt_part_of_ta | T_throw_completion, anode)

        return env0.with_expr_type_replaced(vara, s_dot_field(normal_part_of_ta, '[[Value]]'))

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 8 Syntax-Directed Operations

# ==============================================================================
#@ 8.5.1 Static Semantics: Contains

@P(r"{CONDITION_1} : {LOCAL_REF} Contains {G_SYM}") # spec bug: should say "is *true*"
class _:
    def s_cond(cond, env0, asserting):
        [local_ref, g_sym] = cond.children
        env0.assert_expr_is_of_type(local_ref, T_Parse_Node)
        return (env0, env0)

@P(r"{NAMED_OPERATION_INVOCATION} : {LOCAL_REF} Contains {var}")
@P(r"{NAMED_OPERATION_INVOCATION} : {LOCAL_REF} Contains {G_SYM}")
class _:
    def s_expr(expr, env0, _):
        [lhs, rhs] = expr.children
        return tc_sdo_invocation('Contains', lhs, [rhs], expr, env0)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 9 Executable Code and Execution Contexts

# ==============================================================================
#@ 9.1 Environment Records

def type_for_environment_record_kind(kind):
    return HierType(kind.source_text() + ' Environment Record')

@P('{VAL_DESC} : an Environment Record')
class _:
    s_tb = T_Environment_Record

@P('{VAL_DESC} : an? {ENVIRONMENT_RECORD_KIND} Environment Record')
class _:
    def s_tb(val_desc, env):
        [kind] = val_desc.children
        return type_for_environment_record_kind(kind)

@P(r'{EXPR} : a new {ENVIRONMENT_RECORD_KIND} Environment Record containing no bindings')
@P(r'{EXPR} : a new {ENVIRONMENT_RECORD_KIND} Environment Record')
class _:
    def s_expr(expr, env0, _):
        [kind] = expr.children
        t = type_for_environment_record_kind(kind)
        return (t, env0)

# ==============================================================================
#@ 9.1.1.1 Declarative Environment Records

@P(r"{COMMAND} : Create an immutable binding in {var} for {var} and record that it is uninitialized. If {var} is *true*, record that the newly created binding is a strict binding.")
@P(r"{COMMAND} : Create a mutable binding in {var} for {var} and record that it is uninitialized. If {var} is *true*, record that the newly created binding may be deleted by a subsequent DeleteBinding call.")
class _:
    def s_nv(anode, env0):
        [er_var, n_var, s_var] = anode.children
        env0.assert_expr_is_of_type(er_var, T_Environment_Record)
        env0.assert_expr_is_of_type(n_var, T_String)
        env0.assert_expr_is_of_type(s_var, T_Boolean)
        return env0

@P(r"{COMMAND} : {h_emu_not_ref_Record} that the binding for {var} in {var} has been initialized.")
class _:
    def s_nv(anode, env0):
        [_, key_var, oer_var] = anode.children
        env0.assert_expr_is_of_type(key_var, T_String)
        env0.assert_expr_is_of_type(oer_var, T_Environment_Record)
        return env0

@P(r"{COMMAND} : Remove the binding for {var} from {var}.")
class _:
    def s_nv(anode, env0):
        [n_var, er_var] = anode.children
        env0.assert_expr_is_of_type(n_var, T_String)
        env0.assert_expr_is_of_type(er_var, T_Environment_Record)
        return env0

@P(r"{CONDITION_1} : {var} does not already have a binding for {var}")
@P(r"{CONDITION_1} : {var} does not have a binding for {var}")
@P(r"{CONDITION_1} : {var} has a binding for {var}")
@P(r"{CONDITION_1} : {var} must have an uninitialized binding for {var}")
class _:
    def s_cond(cond, env0, asserting):
        [er_var, n_var] = cond.children
        env0.assert_expr_is_of_type(er_var, T_Environment_Record)
        env0.assert_expr_is_of_type(n_var, T_String)
        return (env0, env0)

@P(r"{CONDITION_1} : the binding for {var} in {var} cannot be deleted")
@P(r"{CONDITION_1} : the binding for {var} in {var} has not yet been initialized")
@P(r"{CONDITION_1} : the binding for {var} in {var} is a mutable binding")
@P(r"{CONDITION_1} : the binding for {var} in {var} is a strict binding")
@P(r"{CONDITION_1} : the binding for {var} in {var} is an uninitialized binding")
class _:
    def s_cond(cond, env0, asserting):
        [n_var, er_var] = cond.children
        env0.assert_expr_is_of_type(n_var, T_String)
        env0.assert_expr_is_of_type(er_var, T_Environment_Record)
        return (env0, env0)

@P(r"{EXPR} : the value currently bound to {var} in {var}")
@P(r"{SETTABLE} : the bound value for {var} in {var}")
class _:
    def s_expr(expr, env0, _):
        [n_var, er_var] = expr.children
        env0.assert_expr_is_of_type(n_var, T_String)
        env0.assert_expr_is_of_type(er_var, T_Environment_Record)
        return (T_Tangible_, env0)

    # 9.1.1.1.5 SetMutableBinding
@P(r"{COMMAND} : Change its bound value to {var}.")
class _:
    def s_nv(anode, env0):
        # elliptical
        [var] = anode.children
        env0.assert_expr_is_of_type(var, T_Tangible_)
        return env0

    # 9.1.1.1.5 SetMutableBinding
@P(r"{CONDITION_1} : This is an attempt to change the value of an immutable binding")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

# ==============================================================================
#@ 9.1.1.4 Global Environment Records

@P(r"{CONDITION_1} : the binding exists")
class _:
    def s_cond(cond, env0, asserting):
        # elliptical
        [] = cond.children
        return (env0, env0)

@P(r"{CONDITION_1} : it must be in the Object Environment Record")
class _:
    def s_cond(cond, env0, asserting):
        # elliptical
        [] = cond.children
        return (env0, env0)

# ==============================================================================
#@ 9.1.1.5 Module Environment Records

@P(r'{COMMAND} : Create an immutable indirect binding in {var} for {var} that references {var} and {var} as its target binding and record that the binding is initialized.')
class _:
    def s_nv(anode, env0):
        [er_var, n_var, m_var, n2_var] = anode.children
        env0.assert_expr_is_of_type(er_var, T_Environment_Record)
        env0.assert_expr_is_of_type(n_var, T_String)
        env0.assert_expr_is_of_type(m_var, T_Module_Record)
        env0.assert_expr_is_of_type(n2_var, T_String)
        return env0

@P(r"{CONDITION_1} : the binding for {var} is an indirect binding")
class _:
    def s_cond(cond, env0, asserting):
        # todo: make ER explicit in spec?
        [n_var] = cond.children
        env0.assert_expr_is_of_type(n_var, T_String)
        return (env0, env0)

@P(r'{CONDITION_1} : When {SETTABLE} is instantiated, it will have a direct binding for {var}')
class _:
    def s_cond(cond, env0, asserting):
        [settable, var] = cond.children
        env0.assert_expr_is_of_type(settable, T_Environment_Record | T_tilde_empty_)
        env0.assert_expr_is_of_type(var, T_String)
        return (env0, env0)

# ==============================================================================
#@ 9.2 PrivateEnvironment Records

@P('{VAL_DESC} : a PrivateEnvironment Record')
class _:
    s_tb = T_PrivateEnvironment_Record

# ==============================================================================
#@ 9.3 Realms

@P('{VAL_DESC} : a Realm Record')
class _:
    s_tb = T_Realm_Record

@P(r"{EXPR} : a new Realm Record")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_Realm_Record, env0)

@P(r'{EX} : the current Realm Record')
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_Realm_Record, env0)

@P(r"{CONDITION_1} : {var} and {var} are not the same Realm Record")
class _:
    def s_cond(cond, env0, asserting):
        [avar, bvar] = cond.children
        env0.assert_expr_is_of_type(avar, T_Realm_Record)
        env0.assert_expr_is_of_type(bvar, T_Realm_Record)
        return (env0, env0)

@P('{VAL_DESC} : a Record whose field names are intrinsic keys and whose values are objects')
class _:
    s_tb = T_Intrinsics_Record

    # 9.3.2 CreateIntrinsics
@P(r"{COMMAND} : Set fields of {DOTTING} with the values listed in {h_emu_xref}. {the_field_names_are_the_names_listed_etc}")
class _:
    def s_nv(anode, env0):
        [var, emu_xref, _] = anode.children
        env0.assert_expr_is_of_type(var, T_Intrinsics_Record)
        return env0

# ==============================================================================
#@ 9.4 Execution Contexts

#> An <dfn>execution context</dfn> is a specification device
#> that is used to track the runtime evaluation of code
#> by an ECMAScript implementation.

@P('{VAL_DESC} : an execution context')
class _:
    s_tb = T_execution_context

@P('{VAL_DESC} : an ECMAScript code execution context')
class _:
    s_tb = T_execution_context

@P(r"{EXPR} : a new execution context")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_execution_context, env0)

# ------------------------------------------------------------------------------
#> At any point in time,
#> there is at most one execution context per agent that is actually executing code.
#> This is known as the agent's <dfn>running execution context</dfn>.
#> All references to the running execution context in this specification
#> denote the running execution context of the surrounding agent.

@P(r'{EXPR} : the running execution context')
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_execution_context, env0)

@P(r"{CONDITION_1} : {var} is now the running execution context")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_execution_context)
        return (env0, env0)

@P(r"{CONDITION_1} : {var} is the running execution context again")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_execution_context)
        return (env0, env0)

# ------------------------------------------------------------------------------
#> The <dfn>execution context stack</dfn> is used to track execution contexts.
#> The running execution context is always the top element of this stack.

@P(r'{COMMAND} : Push {var} onto the execution context stack; {var} is now the running execution context.')
class _:
    def s_nv(anode, env0):
        [var1, var2] = anode.children
        assert var1.children == var2.children
        env1 = env0.ensure_expr_is_of_type(var1, T_execution_context)
        return env1

@P(r'{COMMAND} : Remove {var} from the execution context stack and restore the execution context that is at the top of the execution context stack as the running execution context.')
class _:
    def s_nv(anode, env0):
        [var] = anode.children
        env0.assert_expr_is_of_type(var, T_execution_context)
        return env0

@P(r"{COMMAND} : Remove {var} from the execution context stack and restore {var} as the running execution context.")
class _:
    def s_nv(anode, env0):
        [avar, bvar] = anode.children
        env0.assert_expr_is_of_type(avar, T_execution_context)
        env0.assert_expr_is_of_type(bvar, T_execution_context)
        return env0

@P(r"{COMMAND} : Remove {var} from the execution context stack.")
class _:
    def s_nv(anode, env0):
        [avar] = anode.children
        env0.assert_expr_is_of_type(avar, T_execution_context)
        return env0

    # 9.4.1
@P(r'{EXPR} : the topmost execution context on the execution context stack whose ScriptOrModule component is not {LITERAL}')
class _:
    def s_expr(expr, env0, _):
        [literal] = expr.children
        return (T_execution_context, env0)

    # 9.4.1
@P(r'{CONDITION_1} : no such execution context exists')
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

@P(r"{EXPR} : the second to top element of the execution context stack")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_execution_context, env0)

@P(r"{CONDITION_1} : The execution context stack has at least two elements")
@P(r"{CONDITION_1} : The execution context stack is not empty")
@P(r"{CONDITION_1} : the execution context stack is empty")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

# ------------------------------------------------------------------------------
#> Each execution context has at least the state components listed in
#> <emu-xref href="#table-state-components-for-all-execution-contexts"></emu-xref>.

@P(r"{SETTABLE} : the {EXECUTION_CONTEXT_COMPONENT} component of {var}")
@P(r"{SETTABLE} : The {EXECUTION_CONTEXT_COMPONENT} of {var}")
@P(r"{SETTABLE} : the {EXECUTION_CONTEXT_COMPONENT} of {var}")
@P(r"{SETTABLE} : {var}'s {EXECUTION_CONTEXT_COMPONENT}")
class _:
    def s_expr(expr, env0, _):
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

@P(r"{SETTABLE} : the running execution context's {EXECUTION_CONTEXT_COMPONENT}")
@P(r"{SETTABLE} : the {EXECUTION_CONTEXT_COMPONENT} of the running execution context")
class _:
    def s_expr(expr, env0, _):
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

@P(r"{COMMAND} : {h_emu_meta_start}Resume the suspended evaluation of {var}{h_emu_meta_end}. Let {DEFVAR} be the value returned by the resumed computation.")
class _:
    def s_nv(anode, env0):
        [_, ctx_var, _, b_var] = anode.children
        env0.assert_expr_is_of_type(ctx_var, T_execution_context)
        return env0.plus_new_entry(b_var, NormalCompletionType(T_Tangible_) | T_return_completion | T_throw_completion)

@P(r"{COMMAND} : {h_emu_meta_start}Resume the suspended evaluation of {var}{h_emu_meta_end} using {EX} as the result of the operation that suspended it.")
class _:
    def s_nv(anode, env0):
        [_, ctx_var, _, resa_ex] = anode.children
        env0.assert_expr_is_of_type(ctx_var, T_execution_context)
        env1 = env0.ensure_expr_is_of_type(resa_ex, NormalCompletionType(T_Tangible_) | T_throw_completion)
        return env1

@P(r"{COMMAND} : {h_emu_meta_start}Resume the suspended evaluation of {var}{h_emu_meta_end} using {EX} as the result of the operation that suspended it. Let {DEFVAR} be the Completion Record returned by the resumed computation.")
@P(r"{COMMAND} : {h_emu_meta_start}Resume the suspended evaluation of {var}{h_emu_meta_end} using {EX} as the result of the operation that suspended it. Let {DEFVAR} be the value returned by the resumed computation.")
class _:
    def s_nv(anode, env0):
        [_, ctx_var, _, resa_ex, resb_var] = anode.children
        env0.assert_expr_is_of_type(ctx_var, T_execution_context)
        env1 = env0.ensure_expr_is_of_type(resa_ex, NormalCompletionType(T_Tangible_) | T_return_completion | T_throw_completion)
        return env1.plus_new_entry(resb_var, NormalCompletionType(T_Tangible_) | T_throw_completion)

@P(r"{COMMAND} : Resume the context that is now on the top of the execution context stack as the running execution context.")
class _:
    def s_nv(anode, env0):
        [] = anode.children
        return env0

@P(r"{COMMAND} : Resume {var} passing {EX}. If {var} is ever resumed again, let {DEFVAR} be the Completion Record with which it is resumed.")
class _:
    def s_nv(anode, env0):
        [vara, exb, varc, vard] = anode.children
        env0.assert_expr_is_of_type(vara, T_execution_context)
        env1 = env0.ensure_expr_is_of_type(exb, NormalCompletionType(T_Tangible_) | T_throw_completion)
        env1.assert_expr_is_of_type(varc, T_execution_context)
        return env0.plus_new_entry(vard, NormalCompletionType(T_Tangible_ | T_tilde_empty_) | T_throw_completion)

@P(r"{COMMAND} : Suspend {var} and remove it from the execution context stack.")
class _:
    def s_nv(anode, env0):
        [var] = anode.children
        env0.assert_expr_is_of_type(var, T_execution_context)
        return env0

@P(r"{COMMAND} : Suspend the running execution context.")
class _:
    def s_nv(anode, env0):
        [] = anode.children
        return env0

@P(r'{SMALL_COMMAND} : suspend {var}')
class _:
    def s_nv(anode, env0):
        [var] = anode.children
        env0.assert_expr_is_of_type(var, T_execution_context)
        return env0

@P(r'{COMMAND} : Suspend {var}.')
class _:
    def s_nv(anode, env0):
        [var] = anode.children
        return env0.ensure_expr_is_of_type(var, T_execution_context)

@P(r"{COMMAND} : Set {SETTABLE} such that when evaluation is resumed for that execution context, {var} will be called with no arguments.")
class _:
    def s_nv(anode, env0):
        [settable, var] = anode.children
        env0.assert_expr_is_of_type(settable, T_host_defined_)
        env0.assert_expr_is_of_type(var, ProcType((), T_Top_))
        return env0

@P(r'{CONDITION_1} : {var} is not already suspended')
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_execution_context)
        return (env0, env0)

@P(r"{CONDITION_1} : When we return here, {var} has already been removed from the execution context stack and {var} is the currently running execution context")
class _:
    def s_cond(cond, env0, asserting):
        [a_var, b_var] = cond.children
        env0.assert_expr_is_of_type(a_var, T_execution_context)
        env0.assert_expr_is_of_type(b_var, T_execution_context)
        return (env0, env0)

@P(r"{CONDITION_1} : When we reach this step, {var} has already been removed from the execution context stack and {var} is the currently running execution context")
class _:
    def s_cond(cond, env0, asserting):
        [vara, varb] = cond.children
        env0.assert_expr_is_of_type(vara, T_execution_context)
        env0.assert_expr_is_of_type(varb, T_execution_context)
        return (env0, env0)

# ------------------------------------------------------------------------------
#> The value of the Function component
#> of the running execution context
#> is also called the <dfn>active function object</dfn>.

@P('{VAL_DESC} : the active function object')
class _:
    s_tb = a_subset_of(T_function_object_)

@P(r"{EXPR} : the active function object")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_function_object_, env0)

# ------------------------------------------------------------------------------
#> <dfn>ECMAScript code execution contexts</dfn>
#> have the additional state components listed in
#> <emu-xref href="#table-additional-state-components-for-ecmascript-code-execution-contexts"></emu-xref>

@P(r"{EXPR} : a new ECMAScript code execution context")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_execution_context, env0)

# ------------------------------------------------------------------------------
#> Execution contexts representing the evaluation of Generators
#> have the additional state components listed in
#> <emu-xref href="#table-additional-state-components-for-generator-execution-contexts"></emu-xref>.

@P(r"{CONDITION_1} : {var} does not have a Generator component")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_execution_context)
        return (env0, env0)

# ------------------------------------------------------------------------------

    # 10.3.1
@P(r"{COMMAND} : Perform any necessary implementation-defined initialization of {var}.")
class _:
    def s_nv(anode, env0):
        [var] = anode.children
        env0.assert_expr_is_of_type(var, T_execution_context)
        return env0

    # 15.10.3
@P(r"{CONDITION_1} : The current execution context will not subsequently be used for the evaluation of any ECMAScript code or built-in functions. The invocation of Call subsequent to the invocation of this abstract operation will create and push a new execution context before performing any such evaluation")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

    # 15.10.3
@P(r"{COMMAND} : Discard all resources associated with the current execution context.")
class _:
    def s_nv(anode, env0):
        [] = anode.children
        return env0

# ==============================================================================
#@ 9.5 Jobs and Host Operations to Enqueue Jobs

@P('{VAL_DESC} : a Job Abstract Closure')
class _:
    s_tb = T_Job

@P('{VAL_DESC} : a JobCallback Record')
class _:
    s_tb = T_JobCallback_Record

# ==============================================================================
#@ 9.6 InitializeHostDefinedRealm

@P(r"{CONDITION_1} : the host requires use of an exotic object to serve as {var}'s global object")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_Realm_Record)
        return (env0, env0)

@P(r"{CONDITION_1} : the host requires that the `this` binding in {var}'s global scope return an object other than the global object")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_Realm_Record)
        return (env0, env0)

@P(r"{COMMAND} : Create any host-defined global object properties on {var}.")
class _:
    def s_nv(anode, env0):
        [var] = anode.children
        env0.assert_expr_is_of_type(var, T_Object)
        return env0

# ==============================================================================
#@ 9.7 Agents

#> While an agent's executing thread executes jobs,
#> the agent is the <dfn>surrounding agent</dfn>
#> for the code in those jobs.

@P(r'{EXPR} : the Agent Record of the surrounding agent')
@P(r"{EXPR} : the surrounding agent's Agent Record")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_Agent_Record, env0)

@P(r"{CONDITION_1} : This call to Evaluate is not happening at the same time as another call to Evaluate within the surrounding agent")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

#> An <dfn>agent signifier</dfn> is a globally-unique opaque value
#> used to identify an Agent.

@P('{VAL_DESC} : an agent signifier')
class _:
    s_tb = T_agent_signifier_

# ==============================================================================
#@ 9.10 Processing Model of WeakRef and FinalizationRegistry Targets

# 9.10.4.1
@P(r"{SMALL_COMMAND} : perform any host-defined steps for reporting the error")
class _:
    def s_nv(anode, env0):
        [] = anode.children
        return env0

# ==============================================================================
#@ 9.13 CleanupFinalizationRegistry

@P(r"{COMMAND} : Choose any such {var}.")
class _:
    def s_nv(anode, env0):
        [var] = anode.children
        return env0.ensure_expr_is_of_type(var, T_FinalizationRegistryCellRecord_)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 10 Ordinary and Exotic Objects Behaviours

# ==============================================================================
#@ 10.1 Ordinary Object Internal Methods and Internal Slots

set_up_internal_thing('slot', '[[Prototype]]',  T_Object | T_Null)
set_up_internal_thing('slot', '[[Extensible]]', T_Boolean)

# ==============================================================================
#@ 10.2 ECMAScript Function Objects

@P('{VAL_DESC} : an ECMAScript function object')
class _:
    s_tb = a_subset_of(T_function_object_)

@P('{VAL_DESC} : an ECMAScript function')
class _:
    s_tb = a_subset_of(T_function_object_)

    # 10.2.4
@P(r"{CONDITION_1} : {DOTTING} exists and has been initialized")
class _:
    def s_cond(cond, env0, asserting):
        [dotting] = cond.children
        return (env0, env0)

# ==============================================================================
#@ 10.3 Built-in Function Objects

@P('{VAL_DESC} : a built-in function object')
class _:
    s_tb = a_subset_of(T_function_object_)

set_up_internal_thing('slot', '[[InitialName]]', T_Null | T_String)

@P(r"{EX} : *this* value")
@P(r"{EX} : the *this* value")
class _:
    def s_expr(expr, env0, _):
        return (T_Tangible_, env0)

@P(r"{EX} : NewTarget")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_constructor_object_ | T_Undefined, env0)

    # 10.3.1
@P(r"{EXPR} : the Completion Record that is {h_emu_meta_start}the result of evaluating{h_emu_meta_end} {var} in a manner that conforms to the specification of {var}. {var} is the *this* value, {var} provides the named parameters, and the NewTarget value is *undefined*")
class _:
    def s_expr(expr, env0, _):
        [_, _, avar, bvar, cvar, dvar] = expr.children
        assert avar.children == bvar.children
        env0.assert_expr_is_of_type(avar, T_function_object_)
        env0.assert_expr_is_of_type(cvar, T_Tangible_)
        env0.assert_expr_is_of_type(dvar, ListType(T_Tangible_))
        return (NormalCompletionType(T_Tangible_) | T_throw_completion, env0)

    # 10.3.2
@P(r"{EXPR} : the Completion Record that is {h_emu_meta_start}the result of evaluating{h_emu_meta_end} {var} in a manner that conforms to the specification of {var}. The *this* value is uninitialized, {var} provides the named parameters, and {var} provides the NewTarget value")
class _:
    def s_expr(expr, env0, _):
        [_, _, avar, bvar, cvar, dvar] = expr.children
        assert avar.children == bvar.children
        env0.assert_expr_is_of_type(avar, T_function_object_)
        env0.assert_expr_is_of_type(cvar, ListType(T_Tangible_))
        env0.assert_expr_is_of_type(dvar, T_Tangible_)
        return (NormalCompletionType(T_Tangible_) | T_throw_completion, env0)

    # 10.3.3
@P(r"{EXPR} : a List containing the names of all the internal slots that {h_emu_xref} requires for the built-in function object that is about to be created")
class _:
    def s_expr(expr, env0, _):
        [xref] = expr.children
        return (ListType(T_SlotName_), env0)

    # 10.3.3
@P('{VAL_DESC} : some other definition of a function\'s behaviour provided in this specification')
class _:
    s_tb = T_alg_steps

@P('{VAL_DESC} : a set of algorithm steps')
class _:
    s_tb = T_alg_steps

# ==============================================================================
#@ 10.4.1 Bound Function Exotic Objects

@P('{VAL_DESC} : a bound function exotic object')
class _:
    s_tb = T_bound_function_exotic_object_

# ==============================================================================
#@ 10.4.2 Array Exotic Objects

@P('{VAL_DESC} : an Array exotic object')
class _:
    s_tb = T_Array_object_

@P('{VAL_DESC} : an Array')
class _:
    s_tb = T_Array_object_

# ==============================================================================
#@ 10.4.3 String Exotic Objects

@P('{VAL_DESC} : a String exotic object')
class _:
    s_tb = T_String_exotic_object_

# ==============================================================================
#@ 10.4.4 Arguments Exotic Objects

@P('{VAL_DESC} : an arguments exotic object')
class _:
    s_tb = a_subset_of(T_Object)

set_up_internal_thing('slot', '[[ParameterMap]]', T_Object)

# 10.4.4.{2,4}
@P(r"{CONDITION_1} : The following Set will succeed, since formal parameters mapped by arguments objects are always writable")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

    # 10.4.4.3
@P(r"{CONDITION_1} : {var} contains a formal parameter mapping for {var}")
class _:
    def s_cond(cond, env0, asserting):
        [avar, bvar] = cond.children
        env0.assert_expr_is_of_type(avar, T_Object)
        env0.assert_expr_is_of_type(bvar, T_String | T_Symbol)
        return (env0, env0)

# ==============================================================================
#@ 10.4.5 Integer-Indexed Exotic Objects

@P('{VAL_DESC} : an Integer-Indexed exotic object')
class _:
    s_tb = T_Integer_Indexed_object_

set_up_internal_thing('slot', '[[ViewedArrayBuffer]]', T_ArrayBuffer_object_ | T_SharedArrayBuffer_object_)
set_up_internal_thing('slot', '[[ArrayLength]]',       T_MathInteger_)
set_up_internal_thing('slot', '[[ByteOffset]]',        T_MathInteger_)
set_up_internal_thing('slot', '[[ContentType]]',       T_tilde_BigInt_ | T_tilde_Number_)
set_up_internal_thing('slot', '[[TypedArrayName]]',    T_String)
set_up_internal_thing('slot', '[[ByteLength]]',        T_MathInteger_)

# ==============================================================================
#@ 10.4.6 Module Namespace Exotic Objects

@P('{VAL_DESC} : a module namespace exotic object')
class _:
    s_tb = T_Object

# ==============================================================================
# 10.5 Proxy Object Internal Methods and Internal Slots

@P('{VAL_DESC} : a Proxy exotic object')
class _:
    s_tb = T_Proxy_exotic_object_

set_up_internal_thing('slot', '[[ProxyHandler]]', T_Object | T_Null)
set_up_internal_thing('slot', '[[ProxyTarget]]',  T_Object | T_Null)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 11 ECMAScript Language: Source Text

# ==============================================================================
#@ 11.1 Source Text

#> <dfn>ECMAScript source text</dfn> is a sequence of Unicode code points.

@P('{VAL_DESC} : ECMAScript source text')
class _:
    s_tb = T_Unicode_code_points_

@P('{VAL_DESC} : source text')
class _:
    s_tb = T_Unicode_code_points_

# ==============================================================================
#@ 11.1.6 Static Semantics: ParseText

@P(r"{COMMAND} : Attempt to parse {var} using {var} as the goal symbol, and analyse the parse result for any early error conditions. Parsing and early error detection may be interleaved in an implementation-defined manner.")
class _:
    def s_nv(anode, env0):
        [text_var, goal_var] = anode.children
        env0.assert_expr_is_of_type(text_var, T_Unicode_code_points_)
        env0.assert_expr_is_of_type(goal_var, T_grammar_symbol_)
        return env0

@P(r"{CONDITION_1} : the parse succeeded and no early errors were found")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

@P(r"{EXPR} : the Parse Node (an instance of {var}) at the root of the parse tree resulting from the parse")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_grammar_symbol_)
        return (T_Parse_Node, env0)

@P(r"{EXPR} : a List of one or more {ERROR_TYPE} objects representing the parsing errors and/or early errors. If more than one parsing error or early error is present, the number and ordering of error objects in the list is implementation-defined, but at least one must be present")
class _:
    def s_expr(expr, env0, _):
        [error_type] = expr.children
        return (ListType(type_for_ERROR_TYPE(error_type)), env0)

# ==============================================================================
#@ 11.2.1 Directive Prologues and the Use Strict Directive

@P(r'{CONDITION_1} : the Directive Prologue of {PROD_REF} contains a Use Strict Directive')
class _:
    def s_cond(cond, env0, asserting):
        [prod_ref] = cond.children
        # XXX check that prod_ref makes sense
        return (env0, env0)

# ==============================================================================
#@ 11.2.2 Strict Mode Code

@P(r"{CONDITION_1} : the source text matched by {PROD_REF} is contained in strict mode code")
@P(r"{CONDITION_1} : the source text matched by {PROD_REF} is strict mode code")
@P(r"{CONDITION_1} : the source text matched by {var} is strict mode code")
@P(r"{CONDITION_1} : the source text matched by {var} is non-strict code")
class _:
    def s_cond(cond, env0, asserting):
        [prod_ref] = cond.children
        env0.assert_expr_is_of_type(prod_ref, T_Parse_Node)
        return (env0, env0)

@P(r"{CONDITION_1} : the source text matched by the syntactic production that is being evaluated is contained in strict mode code")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

@P(r"{CONDITION_1} : {LOCAL_REF} is contained in strict mode code")
class _:
    def s_cond(cond, env0, asserting):
        [local_ref] = cond.children
        env0.assert_expr_is_of_type(local_ref, T_Parse_Node)
        return (env0, env0)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 13 ECMAScript Language: Expressions

# ==============================================================================
#@ 13.1.1 Static Semantics: Early Errors [for Identifiers]

@P(r"{CONDITION_1} : {NAMED_OPERATION_INVOCATION} is the StringValue of any |ReservedWord| except for `yield` or `await`")
class _:
    def s_cond(cond, env0, asserting):
        [noi] = cond.children
        env0.assert_expr_is_of_type(noi, T_String)
        return (env0, env0)

# ==============================================================================
#@ 13.3.6.1 Runtime Semantics: Evaluation [of Function Calls]

#> A |CallExpression| evaluation that executes step
#> <emu-xref href="#step-callexpression-evaluation-direct-eval"></emu-xref>
#> is a <dfn>direct eval</dfn>

@P(r"{CONDITION_1} : the source text containing {G_SYM} is eval code that is being processed by a direct eval")
class _:
    def s_cond(cond, env0, asserting):
        [g_sym] = cond.children
        return (env0, env0)

# ==============================================================================
#@ 13.15.2 Runtime Semantics: Evaluation [of Assignment Operators]

# for PR #1961 compound_assignment
@P(r"{MULTILINE_EXPR} : the {TABLE_RESULT_TYPE} associated with {var} in the following table:{_indent_}{nlai}{h_figure}{_outdent_}")
class _:
    def s_expr(expr, env0, _):
        [table_result_type, var, h_figure] = expr.children
        table_result_type_str = table_result_type.source_text()
        if table_result_type_str == 'sequence of Unicode code points':
            result_type = T_Unicode_code_points_
        else:
            assert 0, table_result_type_str
        return (result_type, env0)

# ==============================================================================
#@ 13.15.3 ApplyStringOrNumericBinaryOperator

@P(r"{MULTILINE_EXPR} : the {TABLE_RESULT_TYPE} associated with {var} and Type({var}) in the following table:{_indent_}{nlai}{h_figure}{_outdent_}")
class _:
    def s_expr(expr, env0, _):
        [table_result_type, vara, varb, h_figure] = expr.children
        table_result_type_str = table_result_type.source_text()
        if table_result_type_str == 'abstract operation':
            # result_type = (
            #     ProcType([T_Number, T_Number], NormalCompletionType(T_Number) | T_throw_completion)
            #     |
            #     ProcType([T_BigInt, T_BigInt], NormalCompletionType(T_BigInt) | T_throw_completion)
            # )
            result_type = ProcType((T_Number|T_BigInt, T_Number|T_BigInt), NormalCompletionType(T_Number|T_BigInt) | T_throw_completion)
        else:
            assert 0, table_result_type_str
        return (result_type, env0)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 14 ECMAScript Language: Statements and Declarations

# ==============================================================================
#@ 14.7.5.7 ForIn/OfBodyEvaluation

@P(r"{CONDITION_1} : {var} binds a single name")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        return (env0, env0)

# ==============================================================================
#@ 14.7.5.10 For-In Iterator Objects

@P('{VAL_DESC} : a For-In Iterator')
class _:
    s_tb = T_Iterator_object_

# ==============================================================================
#@ 14.16 The `debugger` Statement

@P(r"{CONDITION_1} : an implementation-defined debugging facility is available and enabled")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

@P(r"{COMMAND} : Perform an implementation-defined debugging action.")
class _:
    def s_nv(anode, env0):
        [] = anode.children
        return env0

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 15 ECMAScript Language: Functions and Classes

# ==============================================================================
#@ 15.7.1 Static Semantics: Early Errors [for Class Definitions]

@P(r"{CONDITION_1} : the name is used once for a getter and once for a setter and in no other entries, and the getter and setter are either both static or both non-static")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

# ==============================================================================
#@ 15.7.14 Runtime Semantics: ClassDefinitionEvaluation

@P(r"{CONDITION_1} : This is only possible for getter/setter pairs")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

@P(r"{EXPR} : the List of arguments that was passed to this function by {dsb_word} or {dsb_word}")
class _:
    def s_expr(expr, env0, _):
        [dsbwa, dsbwb] = expr.children
        assert dsbwa.source_text() == '[[Call]]'
        assert dsbwb.source_text() == '[[Construct]]'
        return (ListType(T_Tangible_), env0)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 16 ECMAScript Language: Scripts and Modules

# ==============================================================================
#@ 16.1.4 Script Records

@P('{VAL_DESC} : a Script Record')
class _:
    s_tb = T_Script_Record

# ==============================================================================
#@ 16.2.1.4 Abstract Module Records

@P('{VAL_DESC} : a Module Record')
class _:
    s_tb = T_Module_Record

@P('{VAL_DESC} : an instance of a concrete subclass of Module Record')
class _:
    s_tb = T_Module_Record

@P(r"{CONDITION_1} : {var} and {var} are the same Module Record")
@P(r"{CONDITION_1} : {var} and {DOTTING} are the same Module Record")
@P(r"{CONDITION_1} : {DOTTING} and {DOTTING} are not the same Module Record")
class _:
    def s_cond(cond, env0, asserting):
        [ex1, ex2] = cond.children
        env0.assert_expr_is_of_type(ex1, T_Module_Record)
        env0.assert_expr_is_of_type(ex2, T_Module_Record)
        return (env0, env0)

@P('{VAL_DESC} : a ResolvedBinding Record')
class _:
    s_tb = T_ResolvedBinding_Record

# ==============================================================================
#@ 16.2.1.5 Cyclic Module Records

@P('{VAL_DESC} : a Cyclic Module Record')
class _:
    s_tb = T_Cyclic_Module_Record

@P('{LIST_ELEMENTS_DESCRIPTION} : Cyclic Module Records')
class _:
    s_tb = T_Cyclic_Module_Record

@P('{VAL_DESC} : a GraphLoadingState Record')
class _:
    s_tb = T_GraphLoadingState_Record

    #@ 16.2.1.5.1.1 InnerModuleLoading
@P(r"{EXPR} : that Record")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        rt = RecordType('', (
                ('[[Specifier]]', T_String),
                ('[[Module]]'   , T_Module_Record),
            )
        )
        return (rt, env0)

    #@ 16.2.1.5.3.1 InnerModuleEvaluation
@P(r"{CONDITION_1} : {DOTTING} is {LITERAL} and was never previously set to {LITERAL}")
class _:
    def s_cond(cond, env0, asserting):
        [dotting, lita, litb] = cond.children
        assert lita.source_text() == '*false*'
        assert litb.source_text() == '*true*'
        env0.assert_expr_is_of_type(dotting, T_Boolean)
        return (env0, env0)

    #@ 16.2.1.5.3.4 AsyncModuleExecutionFulfilled
@P(r"{EXPR} : a List whose elements are the elements of {var}, in the order in which they had their {dsb_word} fields set to {LITERAL} in {cap_word}")
class _:
    def s_expr(expr, env0, _):
        [var, dsb_word, literal, cap_word] = expr.children
        assert dsb_word.source_text() == '[[AsyncEvaluation]]'
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_Cyclic_Module_Record))
        return (ListType(T_Cyclic_Module_Record), env1)

# ==============================================================================
#@ 16.2.1.6 Source Text Module Records

@P('{VAL_DESC} : a Source Text Module Record')
class _:
    s_tb = T_Source_Text_Module_Record

@P('{LIST_ELEMENTS_DESCRIPTION} : Source Text Module Records')
class _:
    s_tb = T_Source_Text_Module_Record

@P('{LIST_ELEMENTS_DESCRIPTION} : ImportEntry Records')
class _:
    s_tb = T_ImportEntry_Record

@P('{LIST_ELEMENTS_DESCRIPTION} : ExportEntry Records')
class _:
    s_tb = T_ExportEntry_Record

@P(r"{CONDITION_1} : {var} provides the direct binding for this export")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_Source_Text_Module_Record)
        return (env0, env0)

@P(r"{CONDITION_1} : {var} imports a specific binding for this export")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_Source_Text_Module_Record)
        return (env0, env0)

#@ 16.2.1.6.2 GetExportedNames
@P(r"{CONDITION_1} : We've reached the starting point of an `export *` circularity")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

    #@ 16.2.1.6.3 ResolveExport
@P(r"{CONDITION_1} : This is a circular import request")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

    #@ 16.2.1.6.3 ResolveExport
@P(r"{CONDITION_1} : A `default` export was not explicitly defined by this module")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

    #@ 16.2.1.6.3 ResolveExport
@P(r"{CONDITION_1} : There is more than one `*` import that includes the requested name")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

    #@ 16.2.1.6.3 ResolveExport
@P(r"{CONDITION_1} : {var} does not provide the direct binding for this export")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_Module_Record)
        return (env0, env0)

    #@ 16.2.1.6.4 InitializeEnvironment
@P(r"{CONDITION_1} : All named exports from {var} are resolvable")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_Source_Text_Module_Record)
        return (env0, env0)

    #@ 16.2.1.6.5 ExecuteModule
@P(r"{CONDITION_1} : {var} has been linked and declarations in its module environment have been instantiated")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_Source_Text_Module_Record)
        return (env0, env0)

# ==============================================================================
#@ 16.2.1.7 GetImportedModule

@P(r"{CONDITION_1} : LoadRequestedModules has completed successfully on {var} prior to invoking this abstract operation")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_Cyclic_Module_Record)
        return (env0, env0)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 18 ECMAScript Standard Built-in Objects

@P(r"{EXPR} : the algorithm steps defined in {h_emu_xref}")
class _:
    def s_expr(expr, env0, _):
        [emu_xref] = expr.children
        return (T_alg_steps, env0)

@P(r"{CONDITION_1} : only one argument was passed")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

@P(r"{EXPR} : the number of non-optional parameters of the function definition in {h_emu_xref}")
class _:
    def s_expr(expr, env0, _):
        [xref] = expr.children
        return (T_MathNonNegativeInteger_, env0)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 19 The Global Object

# for 9.3.4 SetDefaultGlobalBindings
@P(r"{EACH_THING} : property of the Global Object specified in clause {h_emu_xref}")
class _:
    def s_nv(each_thing, env0):
        [emu_xref] = each_thing.children
        # no loop_var!
        return env0

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 20 Fundamental Objects

# ==============================================================================
#@ 20.2.3.5 Function.prototype.toString

@P("{EXPR} : an implementation-defined String source code representation of {var}. The representation must have the syntax of a {nonterminal}. Additionally, if {var} has an {DSBN} internal slot and {DOTTING} is a String, the portion of the returned String that would be matched by {nonterminal} {nonterminal} must be the value of {DOTTING}")
class _:
    def s_expr(expr, env0, _):
        var = expr.children[0]
        env0.assert_expr_is_of_type(var, T_function_object_)
        return (T_String, env0)

@P(r"{EXPR} : an implementation-defined String source code representation of {var}. The representation must have the syntax of a {nonterminal}")
class _:
    def s_expr(expr, env0, _):
        [var, nont] = expr.children
        env0.assert_expr_is_of_type(var, T_function_object_)
        return (T_String, env0)

# ==============================================================================
#@ 20.3 Boolean Objects

set_up_internal_thing('slot', '[[BooleanData]]', T_Boolean)

# ==============================================================================
#@ 20.4 Symbol Objects

set_up_internal_thing('slot', '[[SymbolData]]', T_Symbol)

# ==============================================================================
#@ 20.4.2.2 Symbol.for

@P(r"{EX} : the GlobalSymbolRegistry List")
class _:
    def s_expr(expr, env0, _):
        return (ListType(T_GlobalSymbolRegistry_Record), env0)

@P(r"{CONDITION_1} : GlobalSymbolRegistry does not currently contain an entry for {var}")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_String | T_Symbol)
        return (env0, env0)

# ==============================================================================
#@ 20.5 Error Objects

@P('{LIST_ELEMENTS_DESCRIPTION} : {ERROR_TYPE} objects')
class _:
    def s_tb(led, env):
        [error_type] = led.children
        return type_for_ERROR_TYPE(error_type)

@P('{LIST_ELEMENTS_DESCRIPTION} : errors')
class _:
    s_tb = T_SyntaxError | T_ReferenceError

@P(r"{EX} : a newly created {ERROR_TYPE} object")
class _:
    def s_expr(expr, env0, _):
        [error_type] = expr.children
        return (type_for_ERROR_TYPE(error_type), env0)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 21 Numbers and Dates

# ==============================================================================
#@ 21.1 Number Objects
set_up_internal_thing('slot', '[[NumberData]]', T_Number)

# ==============================================================================
#@ 21.2 BigInt Objects
set_up_internal_thing('slot', '[[BigIntData]]', T_BigInt)

# ==============================================================================
#@ 21.4 Date Objects

# ==============================================================================
#@ 21.4.1 Overview of Date Objects and Definitions of Abstract Operations

# All of the uses of <emu-eqn> to define abstract operations and constants
# appear within this section.
# (Well, except for `floor` in 5.2.5.)

@P(r"{RHSS} : {RHSS}{RHS}")
class _:
    def s_expr(expr, env0, _):
        [rhss, rhs] = expr.children
        (t1, env1) = tc_expr(rhss, env0)
        (t2, env2) = tc_expr(rhs, env1)
        return (t1 | t2, env2)

@P(r"{RHS} : {nlai}= {EXPR} if {CONDITION}")
class _:
    def s_expr(expr, env0, _):
        [subexpr, cond] = expr.children
        (t_env, f_env) = tc_cond(cond, env0)
        (t, env1) = tc_expr(subexpr, t_env)
        return (t, env1)

@P(r"{FACTOR} : {CONSTANT_NAME}")
@P(r"{EX} : {CONSTANT_NAME}")
class _:
    def s_expr(expr, env0, _):
        [constant_name] = expr.children
        constant_name_str = constant_name.source_text()
        # hack:
        result_type = {
            'HoursPerDay'      : T_MathNonNegativeInteger_,
            'MinutesPerHour'   : T_MathNonNegativeInteger_,
            'SecondsPerMinute' : T_MathNonNegativeInteger_,
            'msPerDay'         : T_IntegralNumber_,
            'msPerHour'        : T_IntegralNumber_,
            'msPerMinute'      : T_IntegralNumber_,
            'msPerSecond'      : T_IntegralNumber_,
        }[constant_name_str]
        return (result_type, env0)

# ==============================================================================
#@ 21.4.1.1 Time Values and Time Range

@P('{VAL_DESC} : a time value')
class _:
    s_tb = T_IntegralNumber_

@P('{VAL_DESC} : a finite time value')
class _:
    s_tb = T_IntegralNumber_

# Time value is defined to be 'IntegralNumber_ | NaN_Number_',
# but the only use is for UTC()'s return value,
# which is the result of a subtraction,
# so probably shouldn't be NaN.
# So I've translated it as T_IntegralNumber_.
# I.e., the spec should say "a *finite* time value".

# ==============================================================================
#@ 21.4.1.8 Time Zone Identifiers

@P('{VAL_DESC} : a non-primary time zone identifier in this implementation')
class _:
    s_tb = a_subset_of(T_String)

@P('{EXPR} : the primary time zone identifier associated with {var}')
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_String)
        return (T_String, env0)

@P('{EXPR} : the List of unique available named time zone identifiers')
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (ListType(T_String), env0)

@P("{EXPR} : the String representing the host environment's current time zone, either a primary time zone identifier or an offset time zone identifier")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_String, env0)

# ==============================================================================
#@ 21.4.1.11 Time Zone Identifier Record

@P('{VAL_DESC} : a Time Zone Identifier Record')
@P('{LIST_ELEMENTS_DESCRIPTION} : Time Zone Identifier Records')
class _:
    s_tb = T_Time_Zone_Identifier_Record

# ==============================================================================
#@ 21.4.1.12 AvailableNamedTimeZoneIdentifiers

@P('{CONDITION_1} : the implementation does not include local political rules for any time zones')
@P('{CONDITION_1} : the implementation only supports the UTC time zone')
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

@P('{COMMAND} : Sort {var} into the same order as if an Array of the same values had been sorted using {percent_word} with {LITERAL} as {var}.')
class _:
    def s_nv(anode, env0):
        [list_var, pc_word, comparefn_lit, comparefn_var] = anode.children
        env0.assert_expr_is_of_type(list_var, ListType(T_String))
        return env0

# ==============================================================================
#@ 21.4.1.15 UTC

@P(r"{EX} : the largest integral Number &lt; {var} for which {CONDITION_1} (i.e., {var} represents the last local time before the transition)")
class _:
    def s_expr(expr, env0, _):
        [vara, cond, varb] = expr.children
        # (t_env, f_env) = tc_cond(cond, env0)
        # refers to _possibleInstantsBefore_ which hasn't been defined yet, it's complicated
        return (T_IntegralNumber_, env0)

# ==============================================================================
#@ 21.4.1.17 MakeTime

@P(r"{EXPR} : (({var} `*` msPerHour `+` {var} `*` msPerMinute) `+` {var} `*` msPerSecond) `+` {var}, performing the arithmetic according to IEEE 754-2019 rules (that is, as if using the ECMAScript operators `*` and `+`)")
class _:
    def s_expr(expr, env0, _):
        for var in expr.children:
            env0.assert_expr_is_of_type(var, T_Number)
        return (T_Number, env0)

# ==============================================================================
#@ 21.4.1.18 MakeDay

@P(r"{COMMAND} : Find a finite time value {DEFVAR} such that {CONDITION}; but if this is not possible (because some argument is out of range), return {LITERAL}.")
class _:
    def s_nv(anode, env0):
        [var, cond, literal] = anode.children
        # once, in MakeDay
        env0.assert_expr_is_of_type(literal, T_Number)
        env1 = env0.plus_new_entry(var, T_IntegralNumber_)
        (t_env, f_env) = tc_cond(cond, env1)
        proc_add_return(env1, T_Number, literal)
        return env1

# ==============================================================================
#@ 21.4.2 The Date Constructor

set_up_internal_thing('slot', '[[DateValue]]', T_IntegralNumber_ | T_NaN_Number_)

# ==============================================================================
#@ 21.4.2.1 Date

@P(r"{EXPR} : the time value (UTC) identifying the current time")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_IntegralNumber_, env0)

@P(r"{EXPR} : the result of parsing {var} as a date, in exactly the same manner as for the `parse` method ({h_emu_xref})")
class _:
    def s_expr(expr, env0, _):
        [var, emu_xref] = expr.children
        env0.assert_expr_is_of_type(var, T_String)
        return (T_Number, env0)

# ==============================================================================
#@ 21.4.4 Properties of the Date Prototype Object

@P(r"{EXPR} : this Date object")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_Object | ThrowCompletionType(T_TypeError), env0)

@P(r"{SETTABLE} : the {DSBN} internal slot of this Date object")
class _:
    def s_expr(expr, env0, _):
        [dsbn] = expr.children
        dsbn_name = dsbn.source_text()
        assert dsbn_name == '[[DateValue]]'
        return (T_Number, env0)

# ==============================================================================
#@ 21.4.4.41.2 DateString

@P(r"{EXPR} : the Name of the entry in {h_emu_xref} with the Number {PP_NAMED_OPERATION_INVOCATION}")
class _:
    def s_expr(expr, env0, _):
        [emu_xref, noi] = expr.children
        env1 = env0.ensure_expr_is_of_type(noi, T_IntegralNumber_)
        return (T_String, env1)

# ==============================================================================
#@ 21.4.4.41.3 TimeZoneString

@P(r"{EXPR} : an implementation-defined string that is either {EX} or {EXPR}")
class _:
    def s_expr(expr, env0, _):
        [exa, exb] = expr.children
        env0.assert_expr_is_of_type(exa, T_String)
        env0.assert_expr_is_of_type(exb, T_String)
        return (T_String, env0)

@P(r"{EX} : an implementation-defined timezone name")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_String, env0)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 22 Text Processing

# ==============================================================================
#@ 22.1 String Objects

set_up_internal_thing('slot', '[[StringData]]', T_String)

#@ 22.1.3.28 String.prototype.toLowerCase
@P(r"{EXPR} : the result of toLowercase({var}), according to the Unicode Default Case Conversion algorithm")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_Unicode_code_points_)
        return (T_Unicode_code_points_, env0)

# ==============================================================================
#@ 22.2.1.6 Static Semantics: CharacterValue

@P(r"{EXPR} : the numeric value according to {h_emu_xref}")
class _:
    def s_expr(expr, env0, _):
        return (T_MathInteger_, env0)

# ==============================================================================
#@ 22.2.2 Pattern Semantics

#> In the context of describing the behaviour of a BMP pattern
#> “character” means a single 16-bit Unicode BMP code point.
#> In the context of describing the behaviour of a Unicode pattern
#> “character” means a UTF-16 encoded code point
#> (<emu-xref href="#sec-ecmascript-language-types-string-type"></emu-xref>).
#> In either context, “character value” means the numeric value of the corresponding non-encoded code point.

@P('{VAL_DESC} : a character')
class _:
    s_tb = T_code_unit_ | T_code_point_

@P('{LIST_ELEMENTS_DESCRIPTION} : characters')
class _:
    s_tb = T_character_

@P(r"{EXPR} : the character matched by {PROD_REF}")
class _:
    def s_expr(expr, env0, _):
        [prod_ref] = expr.children
        return (T_character_, env0)

@P(r"{EXPR} : the character whose character value is {var}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_MathInteger_)
        return (T_character_, env1)

@P(r'{EXPR} : the result of applying that mapping to {var}')
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_character_)
        return (T_character_, env1)

@P(r"{EXPR} : the character {SETTABLE}")
class _:
    def s_expr(expr, env0, _):
        [settable] = expr.children
        env1 = env0.ensure_expr_is_of_type(settable, T_character_)
        return (T_character_, env1)

@P(r'{EXPR} : the character value of character {var}')
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_character_)
        return (T_MathInteger_, env0)

# ==============================================================================
#@ 22.2.2.1 Notation

# ------------------------------------------------------------------------------
# CharSet
@P('{VAL_DESC} : a CharSet')
class _:
    s_tb = T_CharSet

@P(r"{COMMAND} : Remove from {var} all characters corresponding to a code point on the right-hand side of the {nonterminal} production.")
class _:
    def s_nv(anode, env0):
        [var, nont] = anode.children
        env0.assert_expr_is_of_type(var, T_CharSet)
        return env0

@P(r'{CONDITION_1} : {var} does not contain exactly one character')
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env1 = env0.ensure_expr_is_of_type(var, T_CharSet)
        return (env1, env1)

@P(r"{CONDITION_1} : {var} and {var} each contain exactly one character")
class _:
    def s_cond(cond, env0, asserting):
        [a,b] = cond.children
        env0.assert_expr_is_of_type(a, T_CharSet)
        env0.assert_expr_is_of_type(b, T_CharSet)
        return (env0, env0)

@P(r'{CONDITION_1} : there exists a member {DEFVAR} of {var} such that {CONDITION_1}')
class _:
    def s_cond(cond, env0, asserting):
        [member_var, set_var, stcond] = cond.children
        env1 = env0.ensure_expr_is_of_type(set_var, T_CharSet)
        env2 = env1.plus_new_entry(member_var, T_character_)
        (t_env, f_env) = tc_cond(stcond, env2)
        assert t_env is f_env
        return (env1, env1)

@P(r'{EXPR} : the one character in CharSet {var}')
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_CharSet)
        return (T_character_, env1)

@P(r'{EXPR} : the CharSet containing all characters with a character value in the inclusive interval from {var} to {var}')
class _:
    def s_expr(expr, env0, _):
        [var1, var2] = expr.children
        env1 = env0.ensure_expr_is_of_type(var1, T_MathInteger_)
        env2 = env0.ensure_expr_is_of_type(var2, T_MathInteger_)
        assert env1 is env0
        assert env2 is env0
        return (T_CharSet, env0)

@P(r"{EXPR} : the CharSet containing the single character {code_point_lit}")
@P(r"{EXPR} : the CharSet containing the single character {var}")
class _:
    def s_expr(expr, env0, _):
        [ex] = expr.children
        env0.ensure_expr_is_of_type(ex, T_character_)
        return (T_CharSet, env0)

@P(r"{EXPR} : the CharSet containing the character matched by {PROD_REF}")
class _:
    def s_expr(expr, env0, _):
        [prod_ref] = expr.children
        return (T_CharSet, env0)

@P(r"{EXPR} : a one-element CharSet containing the character {var}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_character_)
        return (T_CharSet, env0)

@P(r"{EXPR} : the union of CharSets {var}, {var} and {var}")
class _:
    def s_expr(expr, env0, _):
        [va, vb, vc] = expr.children
        enva = env0.ensure_expr_is_of_type(va, T_CharSet)
        envb = env0.ensure_expr_is_of_type(vb, T_CharSet)
        envc = env0.ensure_expr_is_of_type(vc, T_CharSet)
        return (T_CharSet, envs_or([enva, envb, envc]))

@P(r"{EXPR} : the union of {var} and {var}")
@P(r"{EXPR} : the union of CharSets {var} and {var}")
class _:
    def s_expr(expr, env0, _):
        [va, vb] = expr.children
        enva = env0.ensure_expr_is_of_type(va, T_CharSet)
        envb = env0.ensure_expr_is_of_type(vb, T_CharSet)
        return (T_CharSet, env_or(enva, envb))

@P(r"{EXPR} : the CharSet of all characters")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_CharSet, env0)

@P(r"{EXPR} : the ten-element CharSet containing the characters `0`, `1`, `2`, `3`, `4`, `5`, `6`, `7`, `8`, and `9`")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_CharSet, env0)

@P(r"{EXPR} : the CharSet containing every character in {STR_LITERAL}")
class _:
    def s_expr(expr, env0, _):
        [strlit] = expr.children
        return (T_CharSet, env0)

@P(r"{EXPR} : the CharSet containing all characters not in {NAMED_OPERATION_INVOCATION}")
class _:
    def s_expr(expr, env0, _):
        [noi] = expr.children
        env0.assert_expr_is_of_type(noi, T_CharSet)
        return (T_CharSet, env0)

@P(r"{EXPR} : the CharSet containing all characters corresponding to a code point on the right-hand side of the {nonterminal} or {nonterminal} productions")
class _:
    def s_expr(expr, env0, _):
        [nont1, nont2] = expr.children
        return (T_CharSet, env0)

@P(r"{EXPR} : the empty CharSet")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_CharSet, env0)

@P(r"{EXPR} : the CharSet containing all Unicode code points whose character database definition includes the property {var} with value {var}")
class _:
    def s_expr(expr, env0, _):
        [va, vb] = expr.children
        env0.assert_expr_is_of_type(va, ListType(T_code_point_))
        env0.assert_expr_is_of_type(vb, ListType(T_code_point_))
        return (T_CharSet, env0)

@P(r"{EXPR} : the CharSet containing all Unicode code points whose character database definition includes the property “General_Category” with value {var}")
class _:
    def s_expr(expr, env0, _):
        [v] = expr.children
        env0.assert_expr_is_of_type(v, ListType(T_code_point_))
        return (T_CharSet, env0)

@P(r"{EXPR} : the CharSet containing all Unicode code points whose character database definition includes the property {var} with value “True”")
class _:
    def s_expr(expr, env0, _):
        [v] = expr.children
        env0.assert_expr_is_of_type(v, ListType(T_code_point_))
        return (T_CharSet, env0)

@P(r"{EXPR} : the CharSet containing all Unicode code points included in {NAMED_OPERATION_INVOCATION}")
@P(r"{EXPR} : the CharSet containing all Unicode code points not included in {NAMED_OPERATION_INVOCATION}")
class _:
    def s_expr(expr, env0, _):
        [noi] = expr.children
        env0.assert_expr_is_of_type(noi, T_CharSet)
        return (T_CharSet, env0)

@P(r"{EXPR} : the CharSet containing all characters {DEFVAR} such that {var} is not in {var} but {NAMED_OPERATION_INVOCATION} is in {var}")
class _:
    def s_expr(expr, env0, _):
        [loop_var, loop_var2, cs_var, noi, cs_var2] = expr.children
        assert loop_var.source_text() == loop_var2.source_text()
        assert cs_var.source_text() == cs_var2.source_text()
        env0.assert_expr_is_of_type(cs_var, T_CharSet)
        env1 = env0.plus_new_entry(loop_var, T_character_)
        env1.assert_expr_is_of_type(noi, T_character_)
        return (T_CharSet, env0)

@P(r"{NAMED_OPERATION_INVOCATION} : the CharSet returned by {h_emu_grammar}")
class _:
    def s_expr(expr, env0, _):
        [emu_grammar] = expr.children
        return (T_CharSet, env0)

# ------------------------------------------------------------------------------
# CaptureRange

@P(r"{EX} : the CaptureRange {PAIR}")
class _:
    def s_expr(expr, env0, _):
        [pair] = expr.children
        # XXX
        return (T_CaptureRange, env0)

@P(r"{EX} : {var}'s _startIndex_")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_CaptureRange)
        return (T_MathInteger_, env1)

# ------------------------------------------------------------------------------
# MatchState

@P('{VAL_DESC} : a MatchState')
class _:
    s_tb = T_MatchState

@P(r"{EXPR} : the MatchState ({var}, {EX}, {var})")
class _:
    def s_expr(expr, env0, _):
        [input_var, ex, var] = expr.children
        env0.assert_expr_is_of_type(input_var, ListType(T_character_))
        env1 = env0.ensure_expr_is_of_type(ex, T_MathInteger_); assert env1 is env0
        env2 = env0.ensure_expr_is_of_type(var, T_captures_list_); assert env2 is env0
        return (T_MatchState, env0)

@P(r"{EXPR} : {var}'s MatchState")
class _:
    def s_expr(expr, env0, _):
        # todo?: change to Assert: _r_ is a MatchState
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_MatchState)
        return (T_MatchState, env0)

@P(r"{EX} : {var}'s _input_")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_MatchState)
        return (ListType(T_character_), env1)

@P(r"{EX} : {var}'s _endIndex_")
@P(r"{EX} : {var}'s _endIndex_ value")
@P(r"{NUM_COMPARAND} : {var}'s _endIndex_")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_MatchState | T_CaptureRange)
        return (T_MathInteger_, env1)

@P(r"{EX} : {var}'s _captures_ List")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_MatchState)
        return (T_captures_list_, env1)

# ------------------------------------------------------------------------------

@P('{VAL_DESC} : a MatchResult')
class _:
    s_tb = T_MatchResult

@P('{VAL_DESC} : a MatcherContinuation')
class _:
    s_tb = T_MatcherContinuation

@P('{VAL_DESC} : a Matcher')
class _:
    s_tb = T_Matcher

# ==============================================================================
#@ 22.2.2.1.1 RegExp Records

@P('{VAL_DESC} : a RegExp Record')
class _:
    s_tb = T_RegExp_Record

# ==============================================================================
#@ 22.2.2.2 Runtime Semantics: CompilePattern

@P('{VAL_DESC} : an Abstract Closure that takes {VAL_DESC} and {VAL_DESC} and returns {VAL_DESC}')
class _:
    def s_tb(val_desc, env):
        assert val_desc.source_text() == 'an Abstract Closure that takes a List of characters and a non-negative integer and returns a MatchResult'
        return T_RegExpMatcher_

# ==============================================================================
#@ 22.2.2.4 Runtime Semantics: CompileAssertion

@P(r"{CONDITION_1} : the character {EX} is matched by {nonterminal}")
class _:
    def s_cond(cond, env0, asserting):
        [ex, nonterminal] = cond.children
        env0.assert_expr_is_of_type(ex, T_character_)
        assert nonterminal.source_text() == '|LineTerminator|'
        return (env0, env0)

# ==============================================================================
#@ 22.2.2.7.3 Canonicalize

@P(r'{CONDITION_1} : the file {h_a} of the Unicode Character Database provides a simple or common case folding mapping for {var}')
class _:
    def s_cond(cond, env0, asserting):
        [h_a, var] = cond.children
        assert h_a.source_text() == '<a href="https://unicode.org/Public/UCD/latest/ucd/CaseFolding.txt"><code>CaseFolding.txt</code></a>'
        env1 = env0.ensure_expr_is_of_type(var, T_character_)
        return (env1, env1)

@P(r"{EXPR} : the result of toUppercase(« {var} »), according to the Unicode Default Case Conversion algorithm")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_code_point_)
        return (T_Unicode_code_points_, env0)

# ==============================================================================
# 22.2.2.9.3 UnicodeMatchProperty

# Unicode property {name, alias, value, value alias}
@P('{VAL_DESC} : a Unicode property name or property alias listed in the “Property name and aliases” column of {h_emu_xref}')
class _:
    s_tb = a_subset_of(T_Unicode_code_points_)

@P('{VAL_DESC} : a Unicode property name')
class _:
    s_tb = a_subset_of(T_Unicode_code_points_)

@P('{VAL_DESC} : a Unicode property value or property value alias for the General_Category (gc) property listed in {h_a}')
class _:
    s_tb = a_subset_of(T_Unicode_code_points_)

@P('{VAL_DESC} : a Unicode property value')
class _:
    s_tb = a_subset_of(T_Unicode_code_points_)

@P('{VAL_DESC} : a Unicode {h_emu_not_ref_property_name} or property alias listed in the “{h_emu_not_ref_Property_name} and aliases” column of {h_emu_xref} or {h_emu_xref}')
class _:
    s_tb = a_subset_of(T_Unicode_code_points_)

@P('{VAL_DESC} : a binary Unicode property or binary property alias listed in the “Property name and aliases” column of {h_emu_xref}')
class _:
    s_tb = a_subset_of(T_Unicode_code_points_)

@P('{VAL_DESC} : a canonical, unaliased Unicode property name listed in the “Canonical property name” column of {h_emu_xref}')
class _:
    s_tb = a_subset_of(T_Unicode_code_points_)

@P('{VAL_DESC} : a property value or property value alias for the Unicode property {var} listed in {h_a}')
class _:
    def s_tb(val_desc, env):
        [var, h_a] = val_desc.children
        env.assert_expr_is_of_type(var, T_Unicode_code_points_)
        return T_Unicode_code_points_

@P(r"{EXPR} : the canonical {h_emu_not_ref_property_name} of {var} as given in the “Canonical {h_emu_not_ref_property_name}” column of the corresponding row")
class _:
    def s_expr(expr, env0, _):
        [_, v, _] = expr.children
        env0.assert_expr_is_of_type(v, ListType(T_code_point_))
        return (ListType(T_code_point_), env0)

@P(r"{CONDITION_1} : the source text matched by {PROD_REF} is not a Unicode property name or property alias listed in the “Property name and aliases” column of {h_emu_xref}")
class _:
    def s_cond(cond, env0, asserting):
        [prod_ref, h_emu_xref] = cond.children
        return (env0, env0)

@P(r"{CONDITION_1} : the source text matched by {PROD_REF} is not a Unicode property value or property value alias for the General_Category (gc) property listed in {h_a}, nor a binary property or binary property alias listed in the “Property name and aliases” column of {h_emu_xref}")
class _:
    def s_cond(cond, env0, asserting):
        [prod_ref, h_a, h_emu_xref] = cond.children
        return (env0, env0)

@P(r"{CONDITION_1} : the source text matched by {PROD_REF} is not a property value or property value alias for the Unicode property or property alias given by the source text matched by {PROD_REF} listed in {h_a}")
class _:
    def s_cond(cond, env0, asserting):
        [prod_refa, prod_refb, h_a] = cond.children
        return (env0, env0)

# ==============================================================================
#@ 22.2.2.9.4 UnicodeMatchPropertyValue

@P(r"{EXPR} : the canonical property value of {var} as given in the “Canonical property value” column of the corresponding row")
class _:
    def s_expr(expr, env0, _):
        [v] = expr.children
        env0.assert_expr_is_of_type(v, ListType(T_code_point_))
        return (ListType(T_code_point_), env0)

# ==============================================================================
#@ 22.2.3 Abstract Operations for RegExp Creation

set_up_internal_thing('slot', '[[OriginalSource]]', T_String)
set_up_internal_thing('slot', '[[OriginalFlags]]',  T_String)
set_up_internal_thing('slot', '[[RegExpRecord]]',   T_RegExp_Record)
set_up_internal_thing('slot', '[[RegExpMatcher]]',  T_RegExpMatcher_)

# ==============================================================================
#@ 22.2.6.13.1 EscapeRegExpPattern

@P('''{EXPR} : a String in the form of a {nonterminal} ({nonterminal} if {var} contains *"u"*) equivalent to {var} interpreted as UTF-16 encoded Unicode code points ({h_emu_xref}), in which certain code points are escaped as described below. {var} may or may not differ from {var}; however, the Abstract Closure that would result from evaluating {var} as a {nonterminal} ({nonterminal} if {var} contains *"u"*) must behave identically to the Abstract Closure given by the constructed object's {DSBN} internal slot. Multiple calls to this abstract operation using the same values for {var} and {var} must produce identical results''')
class _:
    def s_expr(expr, env0, _):
        # XXX
        return (T_String, env0)

@P(r"{COMMAND} : The code points `/` or any {nonterminal} occurring in the pattern shall be escaped in {var} as necessary to ensure that the string-concatenation of {EX}, {EX}, {EX}, and {EX} can be parsed (in an appropriate lexical context) as a {nonterminal} that behaves identically to the constructed regular expression. For example, if {var} is {STR_LITERAL}, then {var} could be {STR_LITERAL} or {STR_LITERAL}, among other possibilities, but not {STR_LITERAL}, because `///` followed by {var} would be parsed as a {nonterminal} rather than a {nonterminal}. If {var} is the empty String, this specification can be met by letting {var} be {STR_LITERAL}.")
class _:
    def s_nv(anode, env0):
        # XXX
        return env0

# ==============================================================================
#@ 22.2.7.2 RegExpBuiltinExec

@P('{VAL_DESC} : an initialized RegExp instance')
class _:
    s_tb = a_subset_of(T_Object)

@P(r"{EXPR} : the index into {var} of the character that was obtained from element {EX} of {var}")
class _:
    def s_expr(expr, env0, _):
        [list_var, index_var, str_var] = expr.children
        env0.assert_expr_is_of_type(list_var, T_List)
        env0.assert_expr_is_of_type(index_var, T_MathInteger_)
        env0.assert_expr_is_of_type(str_var, T_String) # todo: element of String
        return (T_MathInteger_, env0)

@P(r"{CONDITION_1} : {var} contains any {nonterminal}")
class _:
    def s_cond(cond, env0, asserting):
        [rvar, nonterminal] = cond.children
        env0.assert_expr_is_of_type(rvar, T_Object)
        return (env0, env0)

@P(r"{CONDITION_1} : the {var}<sup>th</sup> capture of {var} was defined with a {nonterminal}")
class _:
    def s_cond(cond, env0, asserting):
        [ivar, rvar, nonterminal] = cond.children
        env0.assert_expr_is_of_type(ivar, T_MathInteger_)
        env0.assert_expr_is_of_type(rvar, T_Object)
        return (env0, env0)

# ==============================================================================
#@ 22.2.7.5 Match Records

@P('{VAL_DESC} : a Match Record')
class _:
    s_tb = T_Match_Record

@P('{LIST_ELEMENTS_DESCRIPTION} : either Match Records or *undefined*')
class _:
    s_tb = T_Match_Record | T_Undefined

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 23 Indexed Collections

# ==============================================================================
#@ 23.1.3.30.1 SortIndexedProperties

@P(r"{COMMAND} : Sort {var} using an implementation-defined sequence of {h_emu_meta_start}calls to {var}{h_emu_meta_end}. If any such call returns an abrupt completion, stop before performing any further calls to {var} and return that Completion Record.")
class _:
    def s_nv(anode, env0):
        [var, _, comparator, _, comparator] = anode.children
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_Tangible_))
        return env1

# ==============================================================================
#@ 23.2 TypedArray Objects

@P('{VAL_DESC} : a TypedArray')
class _:
    s_tb = T_TypedArray_object_

@P('{VAL_DESC} : a TypedArray element type')
class _:
    s_tb = T_TypedArray_element_type

@P('{VAL_DESC} : a String which is the name of a TypedArray constructor in {h_emu_xref}')
class _:
    s_tb = a_subset_of(T_String)

@P(r'{EXPR} : the intrinsic object associated with the constructor name {DOTTING} in {h_emu_xref}')
class _:
    def s_expr(expr, env0, _):
        [dotting, emu_xref] = expr.children
        env0.assert_expr_is_of_type(dotting, T_String)
        return (T_function_object_, env0)

@P(r"{EXPR} : the String value of the Constructor Name value specified in {h_emu_xref} for this <var>TypedArray</var> constructor")
class _:
    def s_expr(expr, env0, _):
        [emu_xref] = expr.children
        return (T_String, env0)

@P(r'{EXPR} : the abstract operation named in the Conversion Operation column in {h_emu_xref} for Element Type {var}')
class _:
    def s_expr(expr, env0, _):
        [emu_xref, var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_TypedArray_element_type)
        return (ProcType((T_Tangible_,), T_IntegralNumber_), env1)

@P(r"{EXPR} : the Element Type value specified in {h_emu_xref} for {EX}")
class _:
    def s_expr(expr, env0, _):
        [emu_xref, ex] = expr.children
        env1 = env0.ensure_expr_is_of_type(ex, T_String)
        return (T_TypedArray_element_type, env0)

@P(r"{EXPR} : the Element Size value specified in {h_emu_xref} for Element Type {var}")
class _:
    def s_expr(expr, env0, _):
        [emu_xref, var] = expr.children
        assert var.source_text() in ['_type_', '_srcType_', '_elementType_']
        env1 = env0.ensure_expr_is_of_type(var, T_TypedArray_element_type)
        return (T_MathInteger_, env1)

@P(r"{EXPR} : the Element Size value specified in {h_emu_xref} for {EX}")
class _:
    def s_expr(expr, env0, _):
        [emu_xref, ex] = expr.children
        env1 = env0.ensure_expr_is_of_type(ex, T_String)
        return (T_MathInteger_, env1)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 24 Keyed Collections

T_MapData_record_ = RecordType( '', (
        ('[[Key]]',   T_Tangible_ | T_tilde_empty_),
        ('[[Value]]', T_Tangible_ | T_tilde_empty_),
    )
)

# 24.1 Map Objects
set_up_internal_thing('slot', '[[MapData]]', ListType(T_MapData_record_))

# 24.2 Set Objects
set_up_internal_thing('slot', '[[SetData]]', ListType(T_Tangible_ | T_tilde_empty_))

# 24.3 WeakMap Objects
set_up_internal_thing('slot', '[[WeakMapData]]', ListType(T_MapData_record_))

# 24.4 WeakSet Objects
set_up_internal_thing('slot', '[[WeakSetData]]', ListType(T_Tangible_ | T_tilde_empty_))

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 25 Structured Data

# ==============================================================================
#@ 25.1 ArrayBuffer Objects

@P('{VAL_DESC} : a read-modify-write modification function')
class _:
    s_tb = T_ReadModifyWrite_modification_closure

@P('{VAL_DESC} : an ArrayBuffer')
class _:
    s_tb = T_ArrayBuffer_object_

@P('{VAL_DESC} : an ArrayBuffer or SharedArrayBuffer')
class _:
    s_tb = T_ArrayBuffer_object_ | T_SharedArrayBuffer_object_

set_up_internal_thing('slot', '[[ArrayBufferData]]',       T_Data_Block | T_Shared_Data_Block | T_Null)
    # XXX but IsSharedArrayBuffer() ensures that ArrayBufferData is a Shared Data Block
set_up_internal_thing('slot', '[[ArrayBufferByteLength]]', T_MathInteger_)
set_up_internal_thing('slot', '[[ArrayBufferDetachKey]]',  T_host_defined_)

# 25.1.2.*
@P(r'{CONDITION_1} : There are sufficient bytes in {var} starting at {var} to represent a value of {var}')
class _:
    def s_cond(cond, env0, asserting):
        [ab_var, st_var, t_var] = cond.children
        env0.assert_expr_is_of_type(ab_var, T_ArrayBuffer_object_ | T_SharedArrayBuffer_object_)
        env0.assert_expr_is_of_type(st_var, T_MathInteger_)
        env0.assert_expr_is_of_type(t_var, T_TypedArray_element_type)
        return (env0, env0)

@P(r"{EX} : a nondeterministically chosen byte value")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_MathNonNegativeInteger_, env0)

@P(r"{EXPR} : a List of length {var} whose elements are nondeterministically chosen byte values")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_MathInteger_)
        return (ListType(T_MathInteger_), env0)

@P('{LIST_ELEMENTS_DESCRIPTION} : byte values')
class _:
    s_tb = a_subset_of(T_MathInteger_)

# ==============================================================================
#@ 25.2 SharedArrayBuffer Objects

@P('{VAL_DESC} : a SharedArrayBuffer')
class _:
    s_tb = T_SharedArrayBuffer_object_

# ==============================================================================
#@ 25.4.1 Waiter Record

@P('{VAL_DESC} : a Waiter Record')
@P('{LIST_ELEMENTS_DESCRIPTION} : Waiter Records')
class _:
    s_tb = T_Waiter_Record

@P(r"{CONDITION_1} : There is no Waiter Record in {DOTTING} whose {dsb_word} field is {EX} and whose {dsb_word} field is {EX}")
class _:
    def s_cond(cond, env0, asserting):
        [list_ex, dsbwa, exa, dsbwb, exb] = cond.children
        env0.assert_expr_is_of_type(list_ex, ListType(T_Waiter_Record))
        assert dsbwa.source_text() == '[[PromiseCapability]]'
        env0.assert_expr_is_of_type(exa, T_PromiseCapability_Record | T_tilde_blocking_)
        assert dsbwb.source_text() == '[[AgentSignifier]]'
        env0.assert_expr_is_of_type(exb, T_agent_signifier_)
        return (env0, env0)

# ==============================================================================
#@ 25.4.2 WaiterList Records

@P('{VAL_DESC} : a WaiterList Record')
class _:
    s_tb = T_WaiterList_Record

#> The agent cluster has a store of WaiterList Records;
#> the store is indexed by (_block_, _i_), where
#> _block_ is a Shared Data Block and _i_ a byte offset into the memory of _block_.
#> WaiterList Records are agent-independent:
#> a lookup in the store of WaiterList Records by (_block_, _i_)
#> will result in the same WaiterList object in any agent in the agent cluster.

@P(r"{EXPR} : the WaiterList Record that is referenced by the pair ({var}, {var})")
class _:
    def s_expr(expr, env0, _):
        [sdb, i] = expr.children
        env0.assert_expr_is_of_type(sdb, T_Shared_Data_Block)
        env0.assert_expr_is_of_type(i, T_MathInteger_)
        return (T_WaiterList_Record, env0)

#> Each WaiterList Record has a <dfn>critical section</dfn> ...

@P(r'{COMMAND} : Wait until no agent is in the critical section for {var}, then enter the critical section for {var} (without allowing any other agent to enter).')
class _:
    def s_nv(anode, env0):
        [var1, var2] = anode.children
        [var_name1] = var1.children
        [var_name2] = var2.children
        assert var_name1 == var_name2
        env1 = env0.ensure_expr_is_of_type(var1, T_WaiterList_Record)
        return env1

@P(r'{COMMAND} : Leave the critical section for {var}.')
class _:
    def s_nv(anode, env0):
        [var] = anode.children
        env0.assert_expr_is_of_type(var, T_WaiterList_Record)
        return env0

@P(r'{CONDITION_1} : The surrounding agent is in the critical section for {var}')
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_WaiterList_Record)
        return (env0, env0)

@P(r'{CONDITION_1} : The surrounding agent is not in the critical section for any WaiterList Record')
class _:
    def s_cond(cond, env0, asserting):
        # nothing to check
        return (env0, env0)

# ==============================================================================
#@ 25.4.3.9 SuspendThisAgent

@P(r"{EXPR} : an implementation-defined non-negative mathematical value")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_MathReal_, env0)

@P(r"{COMMAND} : Perform {PP_NAMED_OPERATION_INVOCATION} and suspend the surrounding agent until the time is {DOTTING}, performing the combined operation in such a way that a notification that arrives after the critical section is exited but before the suspension takes effect is not lost. The surrounding agent can only wake from suspension due to a timeout or due to another agent calling NotifyWaiter with arguments {var} and {var} (i.e. via a call to `Atomics.notify`).")
class _:
    def s_nv(anode, env0):
        [noi, t_var, *blah] = anode.children
        env0.assert_expr_is_of_type(noi, T_tilde_unused_)
        env0.assert_expr_is_of_type(t_var, T_MathReal_ | T_MathPosInfinity_)
        return env0

# ==============================================================================
#@ 25.4.3.10 NotifyWaiter

@P(r"{COMMAND} : Wake the agent whose signifier is {DOTTING} from suspension.")
class _:
    def s_nv(anode, env0):
        [var] = anode.children
        env0.assert_expr_is_of_type(var, T_agent_signifier_)
        return env0

# ==============================================================================
#@ 25.5.1 JSON.parse

@P(r"{COMMAND} : Parse {PP_NAMED_OPERATION_INVOCATION} as a JSON text as specified in ECMA-404. Throw a {ERROR_TYPE} exception if it is not a valid JSON text as defined in that specification.")
class _:
    def s_nv(anode, env0):
        [noi, error_type] = anode.children
        env0.assert_expr_is_of_type(noi, T_Unicode_code_points_)
        return env0

# ==============================================================================
#@ 25.5.2.1 JSON Serialization Record

@P('{VAL_DESC} : a JSON Serialization Record')
class _:
    s_tb = T_JSON_Serialization_Record

# ==============================================================================
#@ 25.5.2.3 QuoteJSONString

@P(r"{CONDITION_1} : {EX} is listed in the “Code Point” column of {h_emu_xref}")
class _:
    def s_cond(cond, env0, asserting):
        [ex, emu_xref] = cond.children
        env0.assert_expr_is_of_type(ex, T_code_point_)
        return (env0, env0)

@P(r"{EX} : the escape sequence for {var} as specified in the “Escape Sequence” column of the corresponding row")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        return (T_String, env0)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 26 Managing Memory

# ==============================================================================
#@ 26.1 WeakRef Objects

@P('{VAL_DESC} : a WeakRef')
class _:
    s_tb = T_WeakRef_object_

set_up_internal_thing('slot', '[[WeakRefTarget]]', T_Object | T_Symbol | T_tilde_empty_)

# ==============================================================================
#@ 26.2 FinalizationRegistry Objects

@P('{VAL_DESC} : a FinalizationRegistry')
class _:
    s_tb = T_FinalizationRegistry_object_

T_FinalizationRegistryCellRecord_ = RecordType('', (
        ('[[WeakRefTarget]]'  , T_Object | T_Symbol | T_tilde_empty_),
        ('[[HeldValue]]'      , T_Tangible_),
        ('[[UnregisterToken]]', T_Object | T_tilde_empty_),
    )
)

set_up_internal_thing('slot', '[[CleanupCallback]]', T_JobCallback_Record)
set_up_internal_thing('slot', '[[Cells]]',           ListType(T_FinalizationRegistryCellRecord_))

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 27 Control Abstraction Objects

# ==============================================================================
#@ 27.1 Iteration

@P('{VAL_DESC} : an Iterator')
class _:
    s_tb = T_Iterator_object_

@P('{VAL_DESC} : an Object that conforms to the <i>IteratorResult</i> interface')
class _:
    s_tb = a_subset_of(T_Object)

# ==============================================================================
#@ 27.2 Promise Objects

@P('{VAL_DESC} : a Promise')
class _:
    s_tb = T_Promise_object_

#@ 27.2.1.1 PromiseCapability Records

@P('{VAL_DESC} : a PromiseCapability Record for an intrinsic {percent_word}')
class _:
    s_tb = T_PromiseCapability_Record

@P('{VAL_DESC} : a PromiseCapability Record')
class _:
    s_tb = T_PromiseCapability_Record

#@ 27.2.1.1.1 IfAbruptRejectPromise

@P(r"{COMMAND} : IfAbruptRejectPromise({var}, {var}).")
class _:
    def s_nv(anode, env0):
        [vara, varb] = anode.children
        env0.assert_expr_is_of_type(varb, T_PromiseCapability_Record)
        (ta, tenv) = tc_expr(vara, env0); assert tenv is env0

        env0.assert_expr_is_of_type(vara, T_Completion_Record)
        (normal_part_of_ta, abnormal_part_of_ta) = ta.split_by(T_normal_completion)

        proc_add_return(env0, T_Promise_object_, anode)
        return env0.with_expr_type_replaced(vara, s_dot_field(normal_part_of_ta, '[[Value]]'))

#@ 27.2.1.2 PromiseReaction Records

@P('{VAL_DESC} : a PromiseReaction Record')
class _:
    s_tb = T_PromiseReaction_Record

@P('{LIST_ELEMENTS_DESCRIPTION} : PromiseReaction Records')
class _:
    s_tb = T_PromiseReaction_Record

#@ 27.2.1.3 CreateResolvingFunctions

T_boolean_value_record_ = RecordType('', (('[[Value]]', T_Boolean),))

set_up_internal_thing('slot', '[[Promise]]',         T_Object)
set_up_internal_thing('slot', '[[AlreadyResolved]]', T_boolean_value_record_)

#@ 27.2.4 Properties of the Promise Constructor

set_up_internal_thing('slot', '[[AlreadyCalled]]',     T_boolean_value_record_ | T_Boolean)
set_up_internal_thing('slot', '[[Index]]',             T_MathInteger_)
set_up_internal_thing('slot', '[[Capability]]',        T_PromiseCapability_Record)
set_up_internal_thing('slot', '[[RemainingElements]]', RecordType('', (('[[Value]]', T_MathInteger_),)))
set_up_internal_thing('slot', '[[Values]]',            ListType(T_Tangible_))
set_up_internal_thing('slot', '[[Errors]]',            ListType(T_Tangible_))

# ==============================================================================
#@ 27.5 Generator Objects

#> A Generator is an instance of a generator function
#> and conforms to both the <i>Iterator</i> and <i>Iterable</i> interfaces.

@P('{VAL_DESC} : a Generator')
class _:
    s_tb = a_subset_of(T_Iterator_object_)

@P('{VAL_DESC} : the execution context of a generator')
class _:
    s_tb = a_subset_of(T_execution_context)

@P(r"{CONDITION_1} : the generator either threw an exception or performed either an implicit or explicit return")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

# 27.{5,6,7}
@P(r"{CONDITION_1} : we return here")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

# ==============================================================================
#@ 27.6 AsyncGenerator Objects

@P('{VAL_DESC} : an AsyncGenerator')
class _:
    s_tb = T_AsyncGenerator_object_

@P(r"{CONDITION_1} : the async generator either threw an exception or performed either an implicit or explicit return")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

@P('{LIST_ELEMENTS_DESCRIPTION} : AsyncGeneratorRequest Records')
class _:
    s_tb = T_AsyncGeneratorRequest_Record

# ==============================================================================
#@ 27.7.5.2 AsyncBlockStart

@P(r"{CONDITION_1} : the async function either threw an exception or performed an implicit or explicit return; all awaiting is done")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 28 Reflection

#@ 28.2.2.1 Proxy.revocable
set_up_internal_thing('slot', '[[RevocableProxy]]', T_Proxy_exotic_object_ | T_Null)

#@ 28.3 Module Namespace Objects
@P('{VAL_DESC} : a Module Namespace Object')
class _:
    s_tb = T_Object

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 29 Memory Model

# ==============================================================================
#@ 29.1 Memory Model Fundamentals

#> A <dfn>Shared Data Block event</dfn> is either
#> a <dfn>ReadSharedMemory</dfn>,
#> <dfn>WriteSharedMemory</dfn>, or
#> <dfn>ReadModifyWriteSharedMemory</dfn> Record.

@P('{VAL_DESC} : a WriteSharedMemory event')
class _:
    s_tb = T_WriteSharedMemory_Event

@P('{VAL_DESC} : a ReadModifyWriteSharedMemory event')
class _:
    s_tb = T_ReadModifyWriteSharedMemory_Event

@P('{VAL_DESC} : a ReadSharedMemory or ReadModifyWriteSharedMemory event')
class _:
    s_tb = T_ReadSharedMemory_Event | T_ReadModifyWriteSharedMemory_Event

@P('{VAL_DESC} : a ReadSharedMemory, WriteSharedMemory, or ReadModifyWriteSharedMemory event')
class _:
    s_tb = T_Shared_Data_Block_Event

@P('{LIST_ELEMENTS_DESCRIPTION} : events')
class _:
    s_tb = T_Event

@P('{LIST_ELEMENTS_DESCRIPTION} : WriteSharedMemory or ReadModifyWriteSharedMemory events')
class _:
    s_tb = T_WriteSharedMemory_Event | T_ReadModifyWriteSharedMemory_Event

@P('{LIST_ELEMENTS_DESCRIPTION} : either WriteSharedMemory or ReadModifyWriteSharedMemory events')
class _:
    s_tb = T_WriteSharedMemory_Event | T_ReadModifyWriteSharedMemory_Event

@P(r"{CONDITION_1} : {var} and {var} are both WriteSharedMemory or ReadModifyWriteSharedMemory events")
class _:
    def s_cond(cond, env0, asserting):
        # XXX spec is ambiguous: "each is A or B" vs "either both A or both B"
        [ea, eb] = cond.children
        (a_t_env, a_f_env) = env0.with_type_test(ea, 'is a', T_WriteSharedMemory_Event | T_ReadModifyWriteSharedMemory_Event, asserting)
        (b_t_env, b_f_env) = env0.with_type_test(eb, 'is a', T_WriteSharedMemory_Event | T_ReadModifyWriteSharedMemory_Event, asserting)
        return (
            env_and(a_t_env, b_t_env),
            env_or(a_f_env, b_f_env)
        )

@P(r"{CONDITION_1} : there exists an event {DEFVAR} such that {CONDITION}")
class _:
    def s_cond(cond, env0, asserting):
        [let_var, stcond] = cond.children
        env_for_cond = env0.plus_new_entry(let_var, T_Shared_Data_Block_Event)
        return tc_cond(stcond, env_for_cond)

#> A <dfn>Synchronize event</dfn> has no fields,
#> and exists purely to directly constrain the permitted orderings of other events.

@P(r"{EXPR} : a new Synchronize event")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_Synchronize_Event, env0)

@P('{VAL_DESC} : a Synchronize event')
class _:
    s_tb = T_Synchronize_Event

@P('{LIST_ELEMENTS_DESCRIPTION} : pairs of Synchronize events')
class _:
    s_tb = T_event_pair_

#> Let the range of
#> a ReadSharedMemory, WriteSharedMemory, or ReadModifyWriteSharedMemory event
#> be the Set of contiguous integers
#> from its [[ByteIndex]] to [[ByteIndex]] + [[ElementSize]] - 1.

@P(r'{CONDITION_1} : {var} has {var} in its range')
class _:
    def s_cond(cond, env0, asserting):
        [sdbe_var, loc_var] = cond.children
        env1 = env0.ensure_expr_is_of_type(sdbe_var, T_Shared_Data_Block_Event)
        env2 = env1.ensure_expr_is_of_type(loc_var, T_MathInteger_)
        return (env2, env2)

@P(r"{CONDITION_1} : {var} and {var} do not have disjoint ranges")
@P(r"{CONDITION_1} : {var} and {var} have equal ranges")
@P(r"{CONDITION_1} : {var} and {var} have overlapping ranges")
class _:
    def s_cond(cond, env0, asserting):
        [ea, eb] = cond.children
        env0.assert_expr_is_of_type(ea, T_Shared_Data_Block_Event)
        env0.assert_expr_is_of_type(eb, T_Shared_Data_Block_Event)
        return (env0, env0)

@P(r"{CONDITION_1} : there exists a WriteSharedMemory or ReadModifyWriteSharedMemory event {DEFVAR} that has {var} in its range such that {CONDITION_1}")
class _:
    def s_cond(cond, env0, asserting):
        [let_var, i, stcond] = cond.children
        env0.assert_expr_is_of_type(i, T_MathInteger_)
        env_for_cond = env0.plus_new_entry(let_var, T_WriteSharedMemory_Event | T_ReadModifyWriteSharedMemory_Event)
        return tc_cond(stcond, env_for_cond)

# ==============================================================================
#@ 29.2 Agent Events Records

@P('{LIST_ELEMENTS_DESCRIPTION} : Agent Events Records')
class _:
    s_tb = T_Agent_Events_Record

@P(r"{EXPR} : the Agent Events Record of {DOTTING} whose {DSBN} is {PP_NAMED_OPERATION_INVOCATION}")
class _:
    def s_expr(expr, env0, _):
        [dotting, dsbn, e] = expr.children
        env0.assert_expr_is_of_type(dotting, ListType(T_Agent_Events_Record))
        assert dsbn.source_text() == '[[AgentSignifier]]'
        env0.assert_expr_is_of_type(e, T_agent_signifier_)
        return (T_Agent_Events_Record, env0)

# ==============================================================================
#@ 29.3 Chosen Value Records

@P('{LIST_ELEMENTS_DESCRIPTION} : Chosen Value Records')
class _:
    s_tb = T_Chosen_Value_Record

# ==============================================================================
#@ 29.4 Candidate Executions

@P('{VAL_DESC} : a candidate execution')
class _:
    s_tb = T_Candidate_Execution_Record

@P('{VAL_DESC} : a candidate execution Record')
class _:
    s_tb = T_Candidate_Execution_Record

# ==============================================================================
#@ 29.5 Abstract Operations for the Memory Model

@P('{VAL_DESC} : a Set of events')
class _:
    s_tb = T_Set

# ==============================================================================
#@ 29.6 Relations of Candidate Executions

#@ 29.6.1 agent-order
@P('{VAL_DESC} : an agent-order Relation')
class _:
    s_tb = T_Relation

#@ 29.6.2 reads-bytes-from
@P('{VAL_DESC} : a reads-bytes-from mathematical function')
class _:
    s_tb = ProcType((T_Event,), ListType(T_WriteSharedMemory_Event | T_ReadModifyWriteSharedMemory_Event))

#@ 29.6.3 reads-from
@P('{VAL_DESC} : a reads-from Relation')
class _:
    s_tb = T_Relation

#@ 29.6.4 host-synchronizes-with
@P('{VAL_DESC} : a host-synchronizes-with Relation')
class _:
    s_tb = T_Relation

#@ 29.6.5 synchronizes-with
@P('{VAL_DESC} : a synchronizes-with Relation')
class _:
    s_tb = T_Relation

#@ 29.6.6 happens-before
@P('{VAL_DESC} : a happens-before Relation')
class _:
    s_tb = T_Relation

# ==============================================================================
#@ 29.8 Races

@P(r"{CONDITION_1} : {var} and {var} are in a race in {var}")
class _:
    def s_cond(cond, env0, asserting):
        [ea, eb, exe] = cond.children
        env0.assert_expr_is_of_type(ea, T_Shared_Data_Block_Event)
        env0.assert_expr_is_of_type(eb, T_Shared_Data_Block_Event)
        env0.assert_expr_is_of_type(exe, T_Candidate_Execution_Record)
        return (env0, env0)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

main()

# vim: sw=4 ts=4 expandtab
