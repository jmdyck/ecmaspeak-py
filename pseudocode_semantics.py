
# ecmaspeak-py/pseudocode_semantics.py:
# Implement the meta-semantics of the ES spec's pseudocode.
#
# Copyright (C) 2018, 2021  J. Michael Dyck <jmdyck@ibiblio.org>

import re, atexit, time, sys, pdb
import collections
import math
import resource
import typing
import unicodedata
from collections import OrderedDict, defaultdict
from itertools import zip_longest
from pprint import pprint
from dataclasses import dataclass, field as dataclass_field

import shared, HTML
from shared import stderr, spec, DL
from Pseudocode_Parser import ANode
from DecoratedFuncDict import DecoratedFuncDict

# static:
from Graph import Graph
from static_types import *

# dynamic:
from E_Value import E_Value, EL_Value, ES_Value
from es_parser import ES_ParseNode, ParseError, T_lit, parse
import unicode_contributory_properties as ucp

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

NYI = 0 # Not Yet Implemented

# If an exception is raised (typically via `assert NYI`),
# only the latest few frames are helpful.
sys.tracebacklimit = 6

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def do_static_type_analysis():
    prep_for_STA()
    levels = compute_dependency_levels()
    do_STA_on_dependency_clusters(levels)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def prep_for_STA():
    stderr('prep_for_STA ...')

    shared.prep_for_line_info()

    set_up_type_tweaks()

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
                # - In the memory model, algorithms that aren't abstract ops
                #   have parameters (sort of), but don't have a header that lists them.
                #
                # - Two Environment Record 'concrete methods' are never called,
                #   so they don't get a structured header.
                #     - (Object Env Rec).CreateImmutableBinding
                #     - (Module Env Rec).DeleteBinding
                pt = convert_nature_to_type(param.nature)

            if param.punct == '[]':
                if header.species.startswith('op:'):
                    # In an abstract operation,
                    # marking a parameter as optional
                    # affects what you can do with it,
                    # and how you can invoke the operation.
                    pt = pt | T_not_passed

                elif header.species.startswith('bif:'):
                    # In a built-in function,
                    # marking a parameter as optional
                    # only affects the default value for the 'length' property.
                    # I.e., the algorithm for a built-in
                    # is not obliged to check whether an optional param is 'present',
                    # it can just use it regardless.
                    # The algorithm *can* do that check on optional params,
                    # but it can also do it on params that aren't marked as optional. E.g.:
                    # - Function's _bodyArg_
                    # - Number's _value_
                    # - String's _value_
                    # - Array.prototype.splice's _start_ & _deleteCount_
                    # - Array.prototype.toSpliced's _start_ & _skipCount_
                    # - GeneratorFunction's _bodyArg_
                    # - AsyncGeneratorFunction's _bodyArg_
                    # - AsyncFunction's _bodyArg_
                    pass

                else:
                    assert 0

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

        self.u_defns = header.u_defns

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
                # defns: {len(self.u_defns)}
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

        e.alg_species = self.species # rarely comes up

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

class TypeTweaks:
    def __init__(self):
        self.tweaks = []
        self.n_uses = 0

type_tweaks_for_op_ = defaultdict(TypeTweaks)

def set_up_type_tweaks():
    type_tweaks_tuples = [
        ('MV'                              , '*return*'        , T_TBD                , T_MathInteger_),
        ('PromiseResolve'                  , '_C_'             , T_constructor_object_, T_Object),

        ('CreateBuiltinFunction'           , '*return*'        , T_function_object_, T_built_in_function_object_),

        ('ClassDefinitionEvaluation',
            '*return*',
            NormalCompletionType(T_function_object_)            | T_abrupt_completion, 
            NormalCompletionType(T_ECMAScript_function_object_ | T_built_in_function_object_) | T_abrupt_completion
        ),
    ]

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
        self.alg_species = None
        self.parret = None
        self.assoc_productions = None
        self.vars = {}
        self.outer = outer

    def __str__(self):
        return str(self.vars)

    def copy(self):
        e = Env(self.outer)
        e.alg_species = self.alg_species
        e.parret = self.parret
        e.assoc_productions = self.assoc_productions
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
        e = self.copy()
        e.vars = {}
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

    e = envs[0].copy()
    e.vars = {}
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

    e = envs[0].copy()
    e.vars = {}

    for env in envs:
        assert env.outer is e.outer
        assert env.alg_species == e.alg_species
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

    parameter_names: typing.Set[str]
    expected_return_type: Type
    returns_completion_records: bool
    return_envs: typing.Set[Env] = dataclass_field(default_factory=set)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def do_STA_on_dependency_clusters(levels):

    atexit.register(write_modified_spec)
    # This was useful when I was gradually building up the set of STA rules,
    # because even if the STA-run ended in an exception (which was usual),
    # I would still get a spec_w_errors written, which might show a little more progress.
    # Now, if STA ends in an exception, spec_w_errors would probably be of no use.

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

    if tah.u_defns == []:
        return False

    final_env = tc_proc(tah.name, tah.u_defns, init_env)

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

    for (i, alg_defn) in enumerate(defns):
        if op_name is not None:
            print()
            print('-' * 20)
            print("%s : defn #%d/%d:" % (op_name, i+1, len(defns)))

        # global trace_this_op
        # trace_this_op = (op_name == 'SV' and i == 27)

        if hasattr(alg_defn, 'emu_grammars'):
            for emu_grammar in alg_defn.emu_grammars:
                if emu_grammar is None:
                    print("(default)")
                else:
                    print(emu_grammar.source_text())
        elif hasattr(alg_defn, 'type_str'):
            print(alg_defn.type_str)
        else:
            print('(no discriminator)')
        print()

        for anode in alg_defn.anodes:

            # kludge:
            if op_name in ['ToObject', 'RequireObjectCoercible']:
                # not ToBigInt
                assert hasattr(alg_defn, 'type_str')
                arg_type = HierType(alg_defn.type_str)
                assert isinstance(arg_type, HierType)
                # in_env = init_env.with_expr_type_narrowed('_argument_', arg_type)
                in_env = init_env.copy()
                in_env.vars['_argument_'] = arg_type

            elif hasattr(alg_defn, 'emu_grammars'):
                productions = []
                for emu_grammar in alg_defn.emu_grammars:
                    if emu_grammar:
                        productions.extend(emu_grammar._gnode._productions)

                in_env = init_env.copy()
                in_env.assoc_productions = productions

            else:
                in_env = init_env

            assert isinstance(anode, ANode)
            if anode.prod.lhs_s in ['{EMU_ALG_BODY}', '{IND_COMMANDS}', '{EE_RULE}', '{ONE_LINE_ALG}']:
                result = tc_nonvalue(anode, in_env)
                assert result is None
            elif anode.prod.lhs_s in ['{EXPR}', '{NAMED_OPERATION_INVOCATION}']:
                (out_t, out_env) = tc_expr(anode, in_env)
                proc_add_return(out_env, out_t, anode)
            else:
                assert 0, anode.prod.lhs_s

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

def convert_nature_node_to_type(nature_node):
    if nature_node is None: return T_TBD

    (_, sup_t) = type_bracket_for(nature_node, None)
    return sup_t

# ------------------------------------------------------------------------------

def type_bracket_for(vd, env):
    assert vd.prod.lhs_s in [
        '{VALUE_DESCRIPTION}',
        '{VAL_DESC_DISJUNCTION}',
        '{VAL_DESC}',
        '{LITERAL_ISH}',
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
        assert result[0].is_a_subtype_of_or_equal_to(result[1])
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

            # Weakref emptying thing, 
            'a List of Objects and/or Symbols': ListType(T_Object | T_Symbol),

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

            'a List of characters': ListType(T_character_),
            'a List of either CaptureRange or *undefined*': ListType(T_CaptureRange | T_Undefined),

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

# ------------------------------------------------------------------------------

def tc_invocation_of_singular_op(callee_op, args, expr, env0):
    assert callee_op.species.startswith('op: singular')

    params = callee_op.parameters_with_types
    (arg_types, env1) = tc_args(params, args, env0, expr)

    if callee_op.name == 'SameValue':
        assert len(arg_types) == 2
        [ta, tb] = arg_types
        check_comparison(expr, 'SameValue', ta, tb)

    return_type = callee_op.return_type

    # In most cases, the type of this invocation
    # is simply the operation's declared return-type.
    # 
    # However, in some cases, we can infer a more precise type
    # based on the specifics of an argument.

    callee_op_name = callee_op.name

    # 5.2.3.1 Completion
    if callee_op_name == 'Completion':
        assert len(args) == 1
        [arg_type] = arg_types
        return_type = arg_type

    # 6.2.4.1 NormalCompletion
    elif callee_op_name == 'NormalCompletion':
        assert len(args) == 1
        [arg_type] = arg_types
        assert arg_type == T_TBD or arg_type.is_a_subtype_of_or_equal_to(T_Normal)
        return_type = NormalCompletionType(arg_type)

    # 6.2.4.2 ThrowCompletion
    elif callee_op_name == 'ThrowCompletion':
        assert len(args) == 1
        [arg_type] = arg_types
        if arg_type == T_TBD: arg_type = T_Normal
        assert arg_type.is_a_subtype_of_or_equal_to(T_Normal)
        return_type = ThrowCompletionType(arg_type)

    # 7.1.5 ToIntegerOrInfinity
    elif callee_op_name == 'ToIntegerOrInfinity':
        assert return_type == NormalCompletionType(T_MathInteger_ | T_MathPosInfinity_ | T_MathNegInfinity_) | T_throw_completion
        # but we can be more precise in some cases

        assert len(args) == 1
        [arg_type] = arg_types

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

    # 7.3.1 MakeBasicObject
    elif callee_op_name == 'MakeBasicObject':
        assert return_type == T_Object
        assert len(args) == 1
        slotnames_arg = args[0]
        slotnames_st = slotnames_arg.source_text()
        if slotnames_st == '« [[Prototype]], [[Extensible]], [[StringData]] »':
            return_type = T_String_exotic_object_
        elif slotnames_st == '« [[ProxyHandler]], [[ProxyTarget]] »':
            return_type = T_Proxy_exotic_object_
        elif slotnames_st == '_internalSlotsList_':
            # Go back a step and (maybe) see what _internalSlotsList_ was set to.
            prev_command = get_previous_command(expr)
            prev_command_st = prev_command.source_text()
            if mo := re.fullmatch(r'Let _internalSlotsList_ be (.+)\.', prev_command_st):
                st = mo.group(1)
                if st == '« [[Prototype]], [[Extensible]], [[ViewedArrayBuffer]], [[TypedArrayName]], [[ContentType]], [[ByteLength]], [[ByteOffset]], [[ArrayLength]] »':
                    return_type = T_TypedArray_object_
                elif st == 'the internal slots listed in <emu-xref href="#table-internal-slots-of-module-namespace-exotic-objects"></emu-xref>':
                    return_type = T_module_namespace_exotic_object_
                elif st == 'the list-concatenation of « [[Prototype]], [[Extensible]] » and the internal slots listed in <emu-xref href="#table-internal-slots-of-bound-function-exotic-objects"></emu-xref>':
                    return_type = T_bound_function_exotic_object_
                else:
                    assert 0, st

    # 7.3.20 CreateListFromArrayLike
    elif callee_op_name == 'CreateListFromArrayLike' and len(args) == 2:
        # The second arg is a list of ES language type names
        # that constrains the return type.
        assert return_type == NormalCompletionType(ListType(T_Tangible_)) | T_throw_completion
        types_arg = args[1]
        assert types_arg.source_text() == '« String, Symbol »'
        return_type = NormalCompletionType(ListType(T_String | T_Symbol)) | T_throw_completion

    # 7.4.8 IteratorClose
    # 7.4.10 AsyncIteratorClose
    elif callee_op_name in ['IteratorClose', 'AsyncIteratorClose']:
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
        [_, cr_arg_type] = arg_types
        return_type = T_throw_completion | cr_arg_type

    # 10.1.12 OrdinaryObjectCreate
    elif callee_op_name == 'OrdinaryObjectCreate':
        assert return_type == T_Object
        assert len(args) in [1, 2]
        proto_arg = args[0]
        proto_st = proto_arg.source_text()
        obj_type = {
            '%AsyncFromSyncIteratorPrototype%'            : T_Object,
            '%AsyncGeneratorFunction.prototype.prototype%': T_AsyncGenerator_object_,
            '%ForInIteratorPrototype%'                    : T_Iterator_object_,
            '%GeneratorFunction.prototype.prototype%'     : T_Generator_object_,
            '%Object.prototype%'                          : T_Object,
            '*null*'                                      : T_Object,
            '_intrinsics_.[[%Object.prototype%]]'         : T_Object,
        }.get(proto_st, T_Object)

        if obj_type == T_Object and len(args) == 2:
            slotnames_arg = args[1]
            slotnames_st = slotnames_arg.source_text()
            if slotnames_st == '_internalSlotsList_':
                prev_command = get_previous_command(expr)
                prev_command_st = prev_command.source_text()
                if mo := re.fullmatch(r'Let _internalSlotsList_ be (.+)\.', prev_command_st):
                    st = mo.group(1)
                    if st == 'the internal slots listed in <emu-xref href="#table-internal-slots-of-ecmascript-function-objects"></emu-xref>':
                        obj_type = T_ECMAScript_function_object_
                    elif st == '« [[GeneratorState]], [[GeneratorContext]], [[GeneratorBrand]] »':
                        obj_type = T_Generator_object_
                    elif st == '« [[AsyncGeneratorState]], [[AsyncGeneratorContext]], [[AsyncGeneratorQueue]], [[GeneratorBrand]] »':
                        obj_type = T_AsyncGenerator_object_
                    else:
                        assert 0, st

        return_type = obj_type

    # 10.1.13 OrdinaryCreateFromConstructor
    elif callee_op_name == 'OrdinaryCreateFromConstructor':
        assert return_type == NormalCompletionType(T_Object) | T_throw_completion
        assert len(args) in [2,3]
        proto_arg = args[1]
        proto_st = proto_arg.source_text()
        obj_type = {
            '*"%AggregateError.prototype%"*'                    : T_AggregateError,
            '*"%ArrayBuffer.prototype%"*'                       : T_ArrayBuffer_object_,
            '*"%AsyncGeneratorFunction.prototype.prototype%"*'  : T_AsyncGenerator_object_,
            '*"%Boolean.prototype%"*'                           : T_Object,
            '*"%DataView.prototype%"*'                          : T_DataView_object_,
            '*"%Date.prototype%"*'                              : T_Object,
            '*"%Error.prototype%"*'                             : T_Error,
            '*"%FinalizationRegistry.prototype%"*'              : T_FinalizationRegistry_object_,
            '*"%GeneratorFunction.prototype.prototype%"*'       : T_Generator_object_,
            '*"%Map.prototype%"*'                               : T_Object,
            '*"%Number.prototype%"*'                            : T_Object,
            '*"%Object.prototype%"*'                            : T_Object,
            '*"%Promise.prototype%"*'                           : T_Promise_object_,
            '*"%RegExp.prototype%"*'                            : T_Object,
            '*"%Set.prototype%"*'                               : T_Object,
            '*"%SharedArrayBuffer.prototype%"*'                 : T_SharedArrayBuffer_object_,
            '*"%WeakMap.prototype%"*'                           : T_WeakMap_object_,
            '*"%WeakRef.prototype%"*'                           : T_WeakRef_object_,
            '*"%WeakSet.prototype%"*'                           : T_WeakSet_object_,
            '<code>"%<var>NativeError</var>.prototype%"</code>' : T_Error,
        }[proto_st]
        return_type = NormalCompletionType(obj_type) | T_throw_completion

    # 25.1.2.9 RawBytesToNumeric
    elif callee_op_name == 'RawBytesToNumeric':
        assert return_type == T_Number | T_BigInt
        assert len(args) == 3
        type_arg = args[0]
        if type_arg.source_text() == '~biguint64~':
            # in SharedArrayBuffer.prototype.grow
            return_type = T_BigInt

    else:
        # Just use {return_type}.
        pass

    return (return_type, env1)

def get_previous_command(expr):
    this_command = expr.closest_containing('{COMMAND}')
    p = this_command.parent
    assert str(p.prod) == "{COMMANDS} : {COMMANDS}{_NL_N} {COMMAND}"
    prev_commands = p.children[0]
    assert str(prev_commands.prod) in [
        "{COMMANDS} : {COMMANDS}{_NL_N} {COMMAND}",
        "{COMMANDS} : {_NL_N} {COMMAND}",
    ]
    prev_command = prev_commands.children[-1]
    return prev_command

# ------------------------------------------------------------------------------

def tc_sdo_invocation(op_name, main_arg, other_args, context, env0):
    op = spec.alg_info_['op'][op_name]
    assert op.species == 'op: discriminated by syntax: steps'

    env1 = env0.ensure_expr_is_of_type(main_arg, T_Parse_Node)
    # XXX expectation should be specific to what the callee accepts

    (_, env2) = tc_args(op.parameters_with_types, other_args, env1, context)

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

    arg_types = []
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
            arg_types.append(arg_type)

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

    return (arg_types, out_env)

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

# ------------------------------------------------------------------------------

def tc_invocation_of_record_method(record_var, method_name_capword, args, context, env0):
    method_name = method_name_capword.source_text()

    callee_op = spec.alg_info_['op'][method_name]
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
        if method_name in rs.addl_method_decls:
            yield rs
            # And don't go any deeper.
            # (In practice, going deeper wouldn't yield any more results,
            # because there's no point re-declaring a method at a deeper level.
            # So this is just an optimization.)
        else:
            # {method_name} is not declared for {rs},
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

    env0 = env0.ensure_expr_is_of_type(record_var, union_of_forp_types)

    params = callee_op.parameters_with_types
    return_type = callee_op.return_type

    (_, env2) = tc_args(params, args, env0, context)
    return (return_type, env2)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def set_up_declared_internal_methods_and_slots():
    # Set up the internal methods and slots
    # that are declared in tables in the spec.
    for emu_table in spec.doc_node.each_descendant_named('emu-table'):
        if 'Internal' in emu_table._caption:
            process_isom_table(emu_table)

# "isom" = "internal slot or method"

def process_isom_table(emu_table):
    cap = emu_table._caption
    if cap == 'Essential Internal Methods':
        holder_stype = T_Object
        must_or_might = 'must have'
        method_or_slot = 'method'

    elif cap == 'Additional Essential Internal Methods of Function Objects':
        holder_stype = T_function_object_
        must_or_might = None # see below
        method_or_slot = 'method'

    elif mo := re.fullmatch(r'Internal Slots of (.+)', cap):
        holder_text = mo.group(1)
        holder_stype = {
            'ECMAScript Function Objects'        : T_ECMAScript_function_object_,
            'Bound Function Exotic Objects'      : T_bound_function_exotic_object_,
            'Module Namespace Exotic Objects'    : T_module_namespace_exotic_object_,
            'For-In Iterator Instances'          : T_Object,
            'Async-from-Sync Iterator Instances' : T_Object,
            'Promise Instances'                  : T_Promise_object_,
            'Generator Instances'                : T_Generator_object_,
            'AsyncGenerator Instances'           : T_AsyncGenerator_object_,
        }[holder_text]
        must_or_might = 'might have' if holder_stype == T_Object else 'must have'
        method_or_slot = 'slot'

    else:
        assert 0, cap

    assert (method_or_slot, emu_table._header_row.cell_texts) in [
        ('method', ['Internal Method', 'Signature', 'Description']),
        ('slot',   ['Internal Slot',   'Type',      'Description']),
    ]

    for row in emu_table._data_rows:
        (isom_name, isom_nature, isom_desc) = row.cell_texts

        if cap == 'Additional Essential Internal Methods of Function Objects':
            # Usually, must_or_might is the same for every row in the table.
            # But that's not true in this table,
            # so we have to set {must_or_might} on a per-row basis.
            if isom_name == '[[Call]]':
                must_or_might = 'must have'
            elif isom_name == '[[Construct]]':
                must_or_might = 'might have'
            else:
                assert 0, isom_name

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

            (param_natures, return_nature) = re.fullmatch(r'\((.+)\) <b>\u2192</b> (.+)', isom_nature).groups()

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

            if isom_name in ['[[PromiseFulfillReactions]]', '[[PromiseRejectReactions]]']:
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

        declare_isom(holder_stype, must_or_might, method_or_slot, isom_name, t)

# ------------------------------------------------------------------------------

def declare_isom(holder_stype, must_or_might, method_or_slot, name, stype):
    decl = IsomDeclaration(holder_stype, must_or_might, method_or_slot, name, stype)
    decls_for_isom_named_[name].append(decl)
    # TODO: Establish that same-name isom_decls have disjoint holder_stype

@dataclass(frozen=True)
class IsomDeclaration:
    holder_stype: Type
    must_or_might: str
    method_or_slot: str
    name: str
    stype: Type

    def __post_init__(self):
        assert self.holder_stype is None or self.holder_stype.is_a_subtype_of_or_equal_to(T_Object)
        assert self.must_or_might in ['must have', 'might have']
        assert self.method_or_slot in ['method', 'slot']
        assert re.fullmatch(r'\[\[[A-Z][a-zA-Z]+\]\]', self.name)
        assert isinstance(self.stype, Type)

decls_for_isom_named_ = defaultdict(list)

# ------------------------------------------------------------------------------

def tb_for_object_with_slot(dsbn):
    dsbn_name = dsbn.source_text()
    isom_decls = decls_for_isom_named_[dsbn_name]
    if len(isom_decls) == 0:
        assert 0, dsbn_name
    elif len(isom_decls) == 1:
        [isom_decl] = isom_decls
        if isom_decl.must_or_might == 'might have':
            tb = a_subset_of(isom_decl.holder_stype)
        else:
            tb = isom_decl.holder_stype
    else:
        tb = union_of_types([
            isom_decl.holder_stype
            for isom_decl in isom_decls
        ])
        if any(
            isom_decl.must_or_might == 'might have'
            for isom_decl in isom_decls
        ):
            tb = a_subset_of(tb)
    return tb

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

class DynamicState:
    def __init__(ds):
        ds.verbosity = 0
        ds.agent = ES_Agent()
        # TODO: handle multiple agents + agent clusters

def reset_dynamic_state():
    global ds
    ds = DynamicState()

    # ---------------------------------------------
    # Executing the pseudocode gets very recursive.

    # In test262-parser-tests, I think the worst (deepest) case is
    # pass/dd3c63403db5c06e.js:
    # ((((((((((((((((((((((((((((((((((((((((((((((((((1))))))))))))))))))))))))))))))))))))))))))))))))))
    #
    # That's 50 pairs of parens, each of which produces a chain of 22 Parse Nodes,
    # so that's 1100 levels of Parse Nodes,
    # plus another 26 for a total of 1126 levels in the parse tree.
    #
    # When executing the 'AllPrivateIdentifiersValid' SDO,
    # each Parse Node level generates about 39 Python stack frames.
    # (For 'Contains', it's only about 35.)
    #
    # 1126 * 39 = 43914

    sys.setrecursionlimit(44_000)

    # and maybe 480 bytes per Python stack frame
    resource.setrlimit(resource.RLIMIT_STACK, (44_000 * 480, resource.RLIM_INFINITY))

    # If you get a Segmentation Fault on this test,
    # enable the tracing block in execute_alg_defn,
    # run `test_parser.py pass/dd3c63403db5c06e.js`
    # and look at the output.

def curr_frame():
    frame_stack = ds.agent.frame_stack
    return frame_stack[-1]

# ------------------------------------------------------------------------------

def get_early_errors_in(pnode):
    if hasattr(ds.agent, 'early_errors'):
        # This is a re-entrant call to this method.
        # So far, the only case I know where this happens
        # is when a Script or Module contains a RegularExpressionLiteral.
        # When determining if the Script/Module has any early errors,
        # you check the rule:
        #   "It is a Syntax Error if
        #   IsValidRegularExpressionLiteral(RegularExpressionLiteral) is false."
        # and IsValidRegularExpressionLiteral calls ParsePattern,
        # which calls ParseText (to parse the REL as a Pattern),
        # which, if the parse succeeds,
        # then has to check the resulting Pattern for early errors.
        assert pnode.symbol == 'Pattern'

        # Now, in a real implementation, you'd *want* any such errors
        # to be part of the early errors for the Script/Module.
        # But that's not how the pseudocode is written.
        #
        # So save the current list of early errors and restore them later.
        # (I'm pretty sure we only need one level of save;
        # if we need more, the following assertion will fail.)
        assert not hasattr(ds.agent, 'saved_early_errors')
        ds.agent.saved_early_errors = ds.agent.early_errors

    ds.agent.early_errors = []
    traverse_for_early_errors(pnode)
    resulting_early_errors = ds.agent.early_errors
    del ds.agent.early_errors

    if hasattr(ds.agent, 'saved_early_errors'):
        ds.agent.early_errors = ds.agent.saved_early_errors
        del ds.agent.saved_early_errors

    return resulting_early_errors

def traverse_for_early_errors(pnode):
    if pnode.is_terminal: return

    if pnode.symbol == 'CoverParenthesizedExpressionAndArrowParameterList':
        # Don't look for early errors within {pnode},
        # because we'll be looking for them within either:
        # - the ParenthesizedExpression that is covered by {pnode}, or
        # - the ArrowFormalParameters that is covered by {pnode}.
        #
        # This is needed to prevent the exponential explosion I was getting with
        # - pass/6b5e7e125097d439.js
        # - pass/714be6d28082eaa7.js
        # - pass/882910de7dd1aef9.js
        # - pass/dd3c63403db5c06e.js
        # which involve things like ((((a)))) but with way more parens.

        return

    ee_map = spec.sdo_coverage_map['Early Errors']

    # check pnode
    if pnode.puk in ee_map:
        ee_rules = ee_map[pnode.puk]
        if ds.verbosity >= 1:
            stderr(f"\nThere are {len(ee_rules)} Early Error rules for {pnode.puk}:")
        for ee_rule in ee_rules:
            execute_alg_defn(ee_rule, focus_node=pnode)

    # check pnode's descendants
    for child in pnode.children:
        traverse_for_early_errors(child)

# ------------------------------------------------------------------------------

def execute_alg_defn(alg_defn, **kwargs):
    frame = Frame(alg_defn, **kwargs)

    frame_stack = ds.agent.frame_stack
    L = len(frame_stack)
    indentation = ' ' * (2 + L)
    if ds.verbosity >= 2: stderr(indentation + 'v', frame._slug)

    frame._tracing_indentation = indentation
    frame._is_tracing = True and (
        frame._slug == 'Early Errors on <ES_ParseNode symbol=UnaryExpression, 2 children>'
    )

    if 0:
        print('len(frame_stack):', L)
        import misc
        py_stack_depth = misc.get_stack_depth()
        print('py stack depth:', py_stack_depth)

        # def tracefunc(*args): print(*args)
        # if py_stack_depth > 18390: sys.settrace(tracefunc)
        print('getrlimit (kb):', resource.getrlimit(resource.RLIMIT_STACK)[0] / 1024)

        f = open('/proc/self/status', 'r')
        for line in f:
            if line.startswith('VmStk'):
                print(line.rstrip())
        f.close()

    frame_stack.append(frame)
    if len(frame_stack) > ds.agent.max_frame_stack_len:
        ds.agent.max_frame_stack_len = len(frame_stack)
    result = frame.run()
    rframe = frame_stack.pop()
    assert rframe is frame

    if ds.verbosity >= 2: stderr(indentation + '^', frame._slug, 'returns', result)
    return result

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

class Frame:
    def __init__(frame, alg_defn, *, focus_node=None, arg_vals=[]):
        # -----
        # alg_defn:

        frame._alg_defn = alg_defn
        frame._header = alg_defn.parent_header
        frame._alg = alg_defn.parent_header.parent_alg

        # -----------
        # focus_node:

        frame._focus_node = focus_node
        if frame._alg.species.startswith('op: discriminated by syntax'):
            assert frame._focus_node is not None
            assert frame._focus_node.isan(ES_ParseNode)
            frame._make_focus_map(frame._focus_node)
        else:
            assert frame._focus_node is None

        # --------
        # arg_vals:

        frame._arg_vals = arg_vals
        if frame._alg.species == 'op: discriminated by syntax: early error':
            assert frame._arg_vals == []

        frame._contours = [{}]
        if frame._header:
            assert len(arg_vals) == len(frame._header.params)
            # XXX Doesn't handle optionals yet.
            for (param, arg_val) in zip(frame._header.params, arg_vals):
                frame.let_var_be_value(param.name, arg_val)
        else:
            assert NYI, frame._alg.name

        # --------

        frame._slug = (
            frame._alg.name
            +
            (f" on {frame._focus_node}" if frame._focus_node else "")
            +
            (f" with args {frame._arg_vals}" if frame._arg_vals else "")
        )

    def _make_focus_map(frame, focus_node):
        frame.focus_map = defaultdict(list)
        for pchild in [focus_node] + focus_node.children:
            if not pchild.is_terminal and pchild.symbol.endswith('?'):
                ref_name = pchild.symbol[:-1]
                if pchild.children:
                    assert len(pchild.children) == 1
                    [ref_node] = pchild.children
                else:
                    ref_node = ES_AbsentParseNode() # ES_ParseNode(T_named('*OMITTED_OPTIONAL*'), (0,0), tip)
            else:
                ref_name = pchild.symbol
                ref_node = pchild

            frame.focus_map[ref_name].append(ref_node)

    def augment_focus_map(frame, pnode):
        # pnode itself should already be in the map:
        assert pnode in frame.focus_map[pnode.symbol]

        # We just need to add its children:
        for pchild in pnode.children:
            assert not pchild.is_terminal
            assert not pchild.symbol.endswith('?')
            ref_name = pchild.symbol
            assert ref_name not in frame.focus_map # otherwise it's weird
            frame.focus_map[ref_name].append(pchild)

    def run(frame):
        anodes = frame._alg_defn.anodes
        # for anode in anodes: stderr('   ', anode.source_text())

        # An alg_defn is allowed to have multiple anodes,
        # but in most cases below, executing multiple anodes
        # would cause the `result` of one anode
        # to be overwritten by the `result` of the next,
        # which is unlikely to be semantically sensible.
        # However, executing multiple {EE_RULE} anodes is fine,
        # because each sets `result` to None, so nothing is lost.
        #
        if len(anodes) > 1:
            assert all(
                anode.prod.lhs_s == '{EE_RULE}'
                for anode in anodes
            )

        for anode in anodes:
            s = anode.prod.lhs_s

            if s == '{EE_RULE}':
                if frame.should_apply_the_rule():
                    try:
                        EXEC(anode, None)
                    except ReferenceToNonexistentThing:
                        # The rule just fails to find an early error.
                        pass
                assert not frame.is_returning()
                result = None

            elif s == '{EMU_ALG_BODY}':
                try:
                    EXEC(anode, None)
                    assert frame.is_returning()
                    result = frame.return_value
                except ReferenceToNonexistentThing:
                    result = {
                        'Contains'  : EL_Boolean(False),
                        'BoundNames': ES_List([]),
                    }[frame._alg.name]

            elif s == '{EXPR}':
                result = EXEC(anode, E_Value)

            elif s == '{ONE_LINE_ALG}':
                EXEC(anode, None)
                assert frame.is_returning()
                result = frame.return_value

            else:
                assert 0, s

        return result

    def should_apply_the_rule(frame):
        if frame._alg_defn.kludgey_p is None: return True

        # kludgey_p hasn't been parsed, so we can't simply run EXEC() on it.

        p_ist = frame._alg_defn.kludgey_p.inner_source_text()
        if p_ist == "In addition to describing an actual object initializer the |ObjectLiteral| productions are also used as a cover grammar for |ObjectAssignmentPattern| and may be recognized as part of a |CoverParenthesizedExpressionAndArrowParameterList|. When |ObjectLiteral| appears in a context where |ObjectAssignmentPattern| is required the following Early Error rules are <b>not</b> applied. In addition, they are not applied when initially parsing a |CoverParenthesizedExpressionAndArrowParameterList| or |CoverCallExpressionAndAsyncArrowHead|.":
            # This <p> precedes two Early Error units,
            # one headed by `PropertyDefinition : CoverInitializedName`,
            # and one headed by the non-empty alternatives for `ObjectLiteral`.
            focus_node = frame._focus_node
            assert focus_node.symbol in ['PropertyDefinition', 'ObjectLiteral']

            def ObjectLiteral_appears_in_a_context_where_ObjectAssignmentPattern_is_required():
                # What is the referent for |ObjectLiteral|?
                if focus_node.symbol == 'PropertyDefinition':
                    # The PropertyDefinition's derivation chain must end with:
                    #     ObjectLiteral -> PropertyDefinitionList+ -> PropertyDefinition.
                    for anc in focus_node.each_ancestor():
                        assert anc.symbol in ['PropertyDefinitionList', 'ObjectLiteral']
                        if anc.symbol == 'ObjectLiteral':
                            ObjectLiteral = anc
                            break
                    else:
                        assert 0
                elif focus_node.symbol == 'ObjectLiteral':
                    # The |ObjectLiteral| in question is just the focus node.
                    ObjectLiteral = focus_node
                else:
                    assert 0
                assert ObjectLiteral.symbol == 'ObjectLiteral'

                # "When |ObjectLiteral| appears in a context where |ObjectAssignmentPattern| is required ..."
                #
                # So when is that?
                #
                # Note that, although the preceding sentence says:
                # "the |ObjectLiteral| productions are also used as a cover grammar for |ObjectAssignmentPattern|"
                # that's not the point where such a covering originates.
                #
                # Instead, it originates in Early Error rules for some (but not all) productions
                # that involve a LeftHandSideExpression:
                #     AssignmentExpression : LeftHandSideExpression `=` AssignmentExpression
                #     DestructuringAssignmentTarget : LeftHandSideExpression
                #     ForInOfStatement : ...
                # In each case, if the LeftHandSideExpression is an ObjectLiteral,
                # then the LeftHandSideExpression is required to cover an AssignmentPattern,
                # which causes the text of the LeftHandSideExpression (and the ObjectLiteral)
                # to be reparsed as an ObjectAssignmentPattern.
                # This situation is presumably what the quoted condition refers to.
                #
                # So we need to:
                # (a) detect whether ObjectLiteral 'is' a LeftHandSideExpression, and then
                # (b) detect whether that LeftHandSideExpression is in one of these productions.

                # (a)
                # The relevant derivation chain is
                # LeftHandSideExpression -> NewExpression -> MemberExpression -> PrimaryExpression -> ObjectLiteral
                four_levels_up = ObjectLiteral.parent.parent.parent.parent
                if four_levels_up.symbol != 'LeftHandSideExpression':
                    # The ObjectLiteral doesn't appear in a context where ObjectAssignmentPattern could be required.
                    return False

                # The ObjectLiteral is unit-derived from a LeftHandSideExpression,
                # so it *might* appear in a contect etc. 
                LeftHandSideExpression = four_levels_up

                # (b)
                parent_production = LeftHandSideExpression.parent.production
                parent_prod_str = f"{parent_production.og_lhs} -> {parent_production.og_rhs_reduced}"
                assert parent_prod_str in [
                    "AssignmentExpression -> LeftHandSideExpression AssignmentOperator AssignmentExpression",
                    "AssignmentExpression -> LeftHandSideExpression `=` AssignmentExpression",
                    "DestructuringAssignmentTarget -> LeftHandSideExpression",
                    "ForInOfStatement -> `for` `(` LeftHandSideExpression `in` Expression `)` Statement",
                    "ForInOfStatement -> `for` `(` LeftHandSideExpression `of` AssignmentExpression `)` Statement",
                    "UpdateExpression -> LeftHandSideExpression",
                ], parent_prod_str
                if parent_prod_str in [
                    "AssignmentExpression -> LeftHandSideExpression `=` AssignmentExpression",
                    "DestructuringAssignmentTarget -> LeftHandSideExpression",
                    "ForInOfStatement -> `for` `(` LeftHandSideExpression `in` Expression `)` Statement",
                    "ForInOfStatement -> `for` `(` LeftHandSideExpression `of` AssignmentExpression `)` Statement",
                    "ForInOfStatement -> `for` `await` `(` LeftHandSideExpression `of` AssignmentExpression `)` Statement",
                ]:
                    # something about LeftHandSideExpression.covered_thing?

                    # The LeftHandSideExpression is in a context that requires it to cover an AssignmentPattern.
                    return True

                else:
                    return False

            def initially_parsing_a_CoverParenthesizedExpressionAndArrowParameterList_or_CoverCallExpressionAndAsyncArrowHead():
                for anc in focus_node.each_ancestor():
                    if anc.symbol in [
                        'CoverParenthesizedExpressionAndArrowParameterList',
                        'CoverCallExpressionAndAsyncArrowHead',
                    ]:
                        return True
                else:
                    return False

            # ----------------------------------------------

            if ObjectLiteral_appears_in_a_context_where_ObjectAssignmentPattern_is_required():
                # ... the following Early Error rules are <b>not</b> applied.
                return False

            if initially_parsing_a_CoverParenthesizedExpressionAndArrowParameterList_or_CoverCallExpressionAndAsyncArrowHead():
                # In addition, they are not applied.
                return False

            return True

        else:
            assert 0

    def is_returning(frame):
        return hasattr(frame, 'return_value')

    def start_returning(frame, return_value):
        assert not frame.is_returning()
        frame.return_value = return_value

    def stop_returning(frame):
        del frame.return_value

    # ------------------------------------------------------

    def start_contour(frame):
        frame._contours.insert(0, {})

    def end_contour(frame):
        frame._contours.pop(0)

    def let_var_be_value(frame, defvar, value):
        if isinstance(defvar, str):
            varname = defvar
        elif isinstance(defvar, ANode):
            assert defvar.prod.lhs_s == '{DEFVAR}'
            [var] = defvar.children
            assert var.prod.lhs_s == '{var}'
            [varname] = var.children
        else:
            assert 0, defvar
        assert all(
            varname not in contour
            for contour in frame._contours
        )
        frame._contours[0][varname] = value

    def set_settable_to_value(frame, settable, value):
        #> Aliases may be modified using the form "Set x to someOtherValue".
        # The following case-analysis probably doesn't belong here.
        p = str(settable.prod)
        if p == '{SETTABLE} : {var}':
            [var] = settable.children
            [varname] = var.children
            assert sum(
                varname in contour
                for contour in frame._contours
            ) == 1
            for contour in frame._contours:
                if varname in contour:
                    contour[varname] = value
        else:
            assert NYI, p

    def get_value_referenced_by_var(frame, varname):
        for contour in frame._contours:
            if varname in contour:
                return contour[varname]
        if varname == '_NcapturingParens_':
            # not defined by a Let anywhere.
            #> _NcapturingParens_ is the total number of left-capturing parentheses
            #> (i.e. the total number of
            #> <emu-grammar>Atom :: `(` GroupSpecifier Disjunction `)`</emu-grammar>
            #> Parse Nodes) in the pattern.
            #> A left-capturing parenthesis is any `(` pattern character
            #> that is matched by the `(` terminal of the
            #> <emu-grammar>Atom :: `(` GroupSpecifier Disjunction `)`</emu-grammar>
            #> production.
            pattern = frame._focus_node.root()
            assert pattern.symbol == 'Pattern'
            n_capturing_parens = 0
            for node in pattern.preorder_traverse():
                if node.is_nonterminal() and node.puk == ('Atom', "`(` GroupSpecifier Disjunction `)`", ''):
                    n_capturing_parens += 1
                    print('432:', node.production)
                    assert 0
            return ES_Mathnum(n_capturing_parens)
        assert 0, f"varname {varname!r} not in any contour!"

    # ------------------------------------------------------

    def has_a_focus_node(frame):
        return (frame._focus_node is not None)

    def resolve_focus_reference(frame, ordinal, nt_name):
        assert frame._alg.species.startswith('op: discriminated by syntax')
        assert frame._focus_node

        if nt_name not in frame.focus_map:
            return ES_AbsentParseNode()

        referents = frame.focus_map[nt_name]
        nr = len(referents)
        if nr == 0:
            assert 0, nt_name

        elif nr == 1:
            assert ordinal is None
            [referent] = referents

        else:
            # The production has more than one occurrence of {nt_name}.
            # Which one are we interested in?

            if nt_name == frame._focus_node.symbol:
                # {nt_name} occurs on both the LHS and RHS.

                # In this case, it would be a bit weird to ask for
                # "the first X" or "the second X", etc.
                # because, does that include the one on the LHS?

                if ordinal == 'derived':
                    # e.g. "the derived |UnaryExpression|"
                    assert nr == 2
                    referent = referents[1]

                elif ordinal is None:
                    assert nr == 2
                    # {nt_name} appears twice, once on LHS and once on RHS.

                    # XXX This approach is fairly kludgey.
                    # The proper approach would involve more static analysis
                    # of the productions in the emu-grammar and the prod-refs in the emu-alg.
                    #
                    # E.g., if <emu-grammar> has
                    #     IdentifierName ::
                    #         IdentifierStart
                    #         IdentifierName IdentifierPart
                    # then you know that a reference to |IdentifierName| must be a reference to the LHS,
                    # because not all RHS have an |IdentifierName|.
                    #
                    # And if the <emu-alg> has references to
                    # "the |UnaryExpression|" and "the derived |UnaryExpression|",
                    # then you can be pretty confident that those are the LHS and the RHS respectively.
                    # (Whereas if you're just looking at "the |UnaryExpression|" in isolation,
                    # you don't know.)
                    #
                    # And if the production is |ImportsList : ImportsList `,` ImportSpecifier|,
                    # and the emu-alg has exactly one reference to "the |ImportsList|"
                    # and exactly one reference to "the |ImportSpecifier|",
                    # then those are probably both RHS refs. (Esp if they're being passed to the same SDO.)
                    # 
                    # And if the production is:
                    #     BindingElementList : BindingElementList `,` BindingElisionElement
                    # The defn of ContainsExpression on that production starts with:
                    #     1. Let _has_ be ContainsExpression of |BindingElementList|.
                    # We know that the |BindingElementList| in that step
                    # can't be a reference to the |BindingElementList| that is the LHS,
                    # because that would lead to infinite recursion.
                    # So it must be a reference to the |BindingElementList| on the RHS.

                    if frame._focus_node.puk in [
                        ('IdentifierName', 'IdentifierName IdentifierPart', ''),
                        ('UnaryExpression', '`delete` UnaryExpression', ''), 
                    ]:
                        referent = referents[0]

                    elif frame._focus_node.puk in [
                        ('BindingPropertyList', 'BindingPropertyList `,` BindingProperty', ''),
                        ('ClassElementList',    'ClassElementList ClassElement', ''),
                        ('FormalParameterList', 'FormalParameterList `,` FormalParameter', ''),
                        ('StatementList',       'StatementList StatementListItem', ''),
                        ('DoubleStringCharacters', 'DoubleStringCharacter DoubleStringCharacters?', '1'),
                        ('ImportsList', 'ImportsList `,` ImportSpecifier', ''),
                        ('ModuleItemList', 'ModuleItemList ModuleItem', ''),
                        ('BindingList', 'BindingList `,` LexicalBinding', ''),
                        ('BindingElementList', 'BindingElementList `,` BindingElisionElement', ''),
                        ('MemberExpression', 'MemberExpression `.` IdentifierName', ''),
                        ('ExportsList', 'ExportsList `,` ExportSpecifier', ''),
                        ('HexDigits', 'HexDigits HexDigit', ''),
                        ('CaseClauses', 'CaseClauses CaseClause', ''),
                        ('VariableDeclarationList', 'VariableDeclarationList `,` VariableDeclaration', ''),
                        ('CallExpression', 'CallExpression `.` IdentifierName', ''),
                        ('TemplateCharacters', 'TemplateCharacter TemplateCharacters?', '1'),
                        ('SingleStringCharacters', 'SingleStringCharacter SingleStringCharacters?', '1'),
                        ('TemplateMiddleList', 'TemplateMiddleList TemplateMiddle Expression', ''),
                        ('PropertyDefinitionList', 'PropertyDefinitionList `,` PropertyDefinition', ''),
                        ('DecimalDigits', 'DecimalDigits DecimalDigit', ''),
                        ('LegacyOctalIntegerLiteral', 'LegacyOctalIntegerLiteral OctalDigit', '')
                    ]:
                        referent = referents[1]

                    else:
                        assert 0, frame._focus_node.puk

                else:
                    assert 0, ordinal

            else:
                # {nt_name} only occurs on the RHS.
                # Here, "the first X" etc is well-defined.
                # I.e., {ordinal} must indicate which we're interested in.
                assert ordinal is not None
                assert 1 <= ordinal <= nr
                referent = referents[ordinal-1]

        if referent.isan(ES_ParseNode):
            assert referent.symbol == nt_name
        elif referent.isan(ES_AbsentParseNode):
            pass
        else:
            assert 0
        return referent

# ------------------------------------------------------------------------------

class ReferenceToNonexistentThing(BaseException):
    def __init__(self, descr):
        self.descr = descr

# For example, consider fail/0bee7999482c66a0.js, whose text is `(10) => 0`
#
# This has a early error due to:
#>   ArrowParameters : CoverParenthesizedExpressionAndArrowParameterList
#>     |CoverParenthesizedExpressionAndArrowParameterList| must cover an |ArrowFormalParameters|.
# (i.e., `(10)` cannot be reparsed as an ArrowFormalParameters)
# That part is all fine.
#
# The problem is that there's also:
#>   ScriptBody : StatementList
#>     It is a Syntax Error if |StatementList| Contains `super` ...
# and in order to evaluate that `Contains`,
# we recurse down to `ArrowParameters`, for which `Contains` is explicitly defined:
#>   1. Let _formals_ be the |ArrowFormalParameters| that is covered by
#>      |CoverParenthesizedExpressionAndArrowParameterList|.
#>   2. Return _formals_ Contains _symbol_.
# but "the |ArrowFormalParameters| that is covered by |...|" is nonexistent.
#
# Of course, it *would* exist if there weren't any (other) early errors, but
# (a) we don't yet know that there's the other early error
#     (because the rules for ScriptBody are checked before those for ArrowParameters), and
# (b) even if we did somehow know that the ArrowParameters rule had found a syntax error,
#     how should that affect the checking of the ScriptBody rule?
#
# I suppose if you were writing rules to allow for this, you would say
# (for Contains at |ArrowParameters|):
#     1. If |CoverParenthesizedExpressionAndArrowParameterList| is not covering an |ArrowFormalParameters|, then
#        1. Return *false*.
#     1. Else,
#        1. [existing rule]
# So is it possible to rejigger execution to accomplish/simulate this?
# (And similar modifications of other rules, e.g. BoundNames.)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def EXEC(anode, expected_return):
    frame = curr_frame()
    assert not frame.is_returning()

    assert isinstance(anode, ANode)

    p = str(anode.prod)
    d_exec = lookup_for_prod(p, 'd_exec')

    if frame._is_tracing: stderr(frame._tracing_indentation, f"before {p}")
    result = d_exec(anode)
    if frame._is_tracing: stderr(frame._tracing_indentation, f"after {p}, returned {result}")

    if expected_return is None:
        expectation_met = (result is None)
    elif expected_return == 'ParseNodeOrAbsent':
        expectation_met = result.isan((ES_ParseNode, ES_AbsentParseNode))
    else:
        expectation_met = isinstance(result, expected_return)

    if not expectation_met:
        # Maybe we can do an implicit conversion
        if expected_return in [ES_Mathnum, (ES_Mathnum,EL_Number)] and result.isan(ES_UnicodeCodePoint):
            if ds.verbosity >= 1: stderr("Implicitly converting ES_UnicodeCodePoint to ES_Mathnum")
            result = ES_Mathnum(result.scalar)
            expectation_met = True

    if not expectation_met:
        stderr()
        stderr(f"After handling:")
        stderr(f"    {anode}")
        stderr(f"result is {result}, but caller expects {expected_return}")
        assert 0
        sys.exit(1)

    return result

# ------------------------------------------------------------------------------

def EACH(each_thing):
    assert not curr_frame().is_returning()

    assert isinstance(each_thing, ANode)

    p = str(each_thing.prod)
    d_each = lookup_for_prod(p, 'd_each')

    (var, iterable) = d_each(each_thing)

    assert isinstance(var, ANode)
    assert var.prod.lhs_s == '{DEFVAR}'
    assert isinstance(iterable, collections.abc.Iterable)

    return (var, iterable)

# ------------------------------------------------------

def value_matches_description(value, description):
    assert value.isan(E_Value)
    assert isinstance(description, ANode)
    assert description.prod.lhs_s in ['{VALUE_DESCRIPTION}', '{VAL_DESC_DISJUNCTION}', '{VAL_DESC}']

    p = str(description.prod)
    d_desc = lookup_for_prod(p, 'd_desc')

    result = d_desc(description, value)
    assert result in [True, False]
    return result

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

predefined_operations = DecoratedFuncDict()

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

def report_unused_entries():
    def dfd_report_unused_entries(dfd_name, dfd):
        print(f"unused entries in {dfd_name}:")
        unused_keys = [
            key
            for (key, count) in dfd.access_counts()
            if count == 0
        ]
        if unused_keys == []:
            print(f"    (none)")
        else:
            for key in unused_keys:
                print(f"    {key}")
        print()

    dfd_report_unused_entries('class_for_prod_str_',   class_for_prod_str_)
    dfd_report_unused_entries('predefined_operations', predefined_operations)

# ------------------------------------------------------------------------------

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

def d_exec_pass_down(anode):
    [child] = anode.children
    return EXEC(child, E_Value)

def d_exec_pass_down_expecting_None(anode):
    [child] = anode.children
    EXEC(child, None)

# Note that, in what follows,
# the classes declared as "class _"
# don't exist to be instantiated,
# they only exist as containers of attributes.

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# Unit productions (and other similar productions)
# where the semantics are just to delegate to a child node.

@P("{IND_COMMANDS} : {_indent_}{COMMANDS}{_outdent_}")
@P("{COMMANDS} : {_NL_N} {COMMAND}")
@P("{COMMAND} : {IF_CLOSED}")
@P("{COMMAND} : {IF_OTHER}")
@P("{ELSE_PART} : Else, {SMALL_COMMAND}.")
@P("{ELSE_PART} : Else,{IND_COMMANDS}")
@P("{ELSE_PART} : Otherwise, {SMALL_COMMAND}.")
@P("{COMMAND} : Perform the following substeps in an implementation-defined order, possibly interleaving parsing and error detection:{IND_COMMANDS}")
@P("{COMMAND} : Optionally, {SMALL_COMMAND}.")
@P("{ONE_LINE_ALG} : {_indent_}{nlai}{COMMAND}{_outdent_}{nlai}")
class _:
    s_nv = s_nv_pass_down
    d_exec = d_exec_pass_down_expecting_None

@P("{EXPR} : the result of {PP_NAMED_OPERATION_INVOCATION}")
@P("{EXPR} : {EX}")
@P("{EX} : ({EX})")
@P("{EX} : The value of {SETTABLE}")
@P("{EX} : the value of {SETTABLE}")
@P("{EX} : {LITERAL_ISH}")
@P("{EX} : {LITERAL}")
@P("{EX} : {LOCAL_REF}")
@P("{EX} : {NUM_EXPR}")
@P("{EX} : {PAIR}")
@P("{EX} : {PP_NAMED_OPERATION_INVOCATION}")
@P("{EX} : {RECORD_CONSTRUCTOR}")
@P("{FACTOR} : ({NUM_EXPR})")
@P("{FACTOR} : {BIGINT_LITERAL}")
@P("{FACTOR} : {MATH_LITERAL}")
@P("{FACTOR} : {NUMBER_LITERAL}")
@P("{FACTOR} : {PP_NAMED_OPERATION_INVOCATION}")
@P("{FACTOR} : {SETTABLE}")
@P("{LITERAL} : {code_point_lit}")
@P("{LOCAL_REF} : {PROD_REF}")
@P("{LOCAL_REF} : {SETTABLE}")
@P("{NAMED_OPERATION_INVOCATION} : {PREFIX_PAREN}")
@P("{NUM_COMPARAND} : {FACTOR}")
@P("{NUM_COMPARAND} : {SUM}")
@P("{NUM_COMPARAND} : {PRODUCT}")
@P("{NUM_EXPR} : {PRODUCT}")
@P("{NUM_EXPR} : {SUM}")
@P("{SETTABLE} : {DOTTING}")
@P("{TERM} : {FACTOR}")
@P("{TERM} : {PRODUCT}")
@P("{TYPE_ARG} : {var}")
class _:
    s_expr = s_expr_pass_down
    d_exec = d_exec_pass_down

@P("{LITERAL} : {MATH_LITERAL}")
@P("{LITERAL} : {NUMBER_LITERAL}")
class _:
    s_tb = s_tb_pass_down
    s_expr = s_expr_pass_down
    d_exec = d_exec_pass_down

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# functions for dealing with spec markup?

def dereference_emu_xref(emu_xref):
    assert isinstance(emu_xref, ANode)
    assert emu_xref.prod.lhs_s == '{h_emu_xref}'
    st = emu_xref.source_text()
    mo = re.fullmatch('<emu-xref href="#([^"]+)">[^<>]*</emu-xref>', st)
    assert mo
    id = mo.group(1)
    return spec.node_with_id_[id]

def emu_table_get_unique_row_satisfying(emu_table, predicate):
    assert isinstance(emu_table, HTML.HNode)
    assert emu_table.element_name == 'emu-table'

    rows_selected_by_predicate = [
        row
        for row in emu_table._data_rows
        if predicate(row)
    ]
    assert len(rows_selected_by_predicate) == 1
    [row] = rows_selected_by_predicate
    return row

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

T_Unicode_code_points_ = ListType(T_code_point_)

@dataclass(frozen=True)
class ES_UnicodeCodePoint(ES_Value):
    scalar: int
    def __init__(self, scalar):
        assert 0 <= scalar <= 0x10ffff
        object.__setattr__(self, 'scalar', scalar)

# --------------------------------------

@P("{VAL_DESC} : a Unicode code point")
@P("{VAL_DESC} : a code point")
@P("{LIST_ELEMENTS_DESCRIPTION} : code points")
class _:
    s_tb = T_code_point_

@P("{VAL_DESC} : the single code point {code_point_lit} or {code_point_lit}")
class _:
    s_tb = a_subset_of(T_Unicode_code_points_)

# --------------------------------------
# expressions that return a code point:

@P(r"{code_point_lit} : ` [^`]+ ` \x20 U \+ [0-9A-F]{4} \x20 \( [A-Z -]+ \)")
@P(r"{code_point_lit} : \b U \+ [0-9A-F]{4} \x20 \( [A-Z -]+ \)")
class _:
    def s_expr(expr, env0, _):
        return (T_code_point_, env0)

@P("{EXPR} : the code point {var}")
        # This means "the code point whose numeric value is {var}"
@P("{EXPR} : the code point whose numeric value is {EX}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_MathInteger_)
        return (T_code_point_, env0)

    def d_exec(expr):
        [noi] = expr.children
        mathnum = EXEC(noi, ES_Mathnum)
        return ES_UnicodeCodePoint(mathnum.val)

@P("{EXPR} : the code point obtained by applying the UTF-8 transformation to {var}, that is, from a List of octets into a 21-bit value")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, ListType(T_MathInteger_))
        return (T_code_point_, env0)

# -----------------------
# conditions that involve a code point:

@P("{CONDITION_1} : {var} has a numeric value less than {code_unit_lit}")
class _:
    def s_cond(cond, env0, asserting):
        [var, code_unit_lit] = cond.children
        env1 = env0.ensure_expr_is_of_type(var, T_code_point_) # odd
        return (env1, env1)

    # for 19.2.6.6
@P("{CONDITION_1} : {var} does not contain a valid UTF-8 encoding of a Unicode code point")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, ListType(T_MathInteger_))
        return (env0, env0)

@P("{CONDITION_1} : {var} has the same numeric value as a leading surrogate or trailing surrogate")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_code_point_)
        return (env0, env0)

# ----------------------------
# other

@P("{EXPR} : the List of octets resulting by applying the UTF-8 transformation to {DOTTING}")
class _:
    def s_expr(expr, env0, _):
        [dotting] = expr.children
        env1 = env0.ensure_expr_is_of_type(dotting, T_code_point_)
        return (ListType(T_MathInteger_), env1)

# ----------------------------------------------------------

def unicode_character_has_property(pychar, property_name):
    # Does the given character (code point) have the given Unicode property?
    assert len(pychar) == 1

    # Python has the unicodedata module, but
    # it doesn't have a method relating to properties.

    # We'll probably need to know pychar's category.
    cat = unicodedata.category(pychar)

    if property_name == 'ID_Start':
        # https://www.unicode.org/Public/UCD/latest/ucd/DerivedCoreProperties.txt:
        #
        #" Derived Property: ID_Start
        #"  Characters that can start an identifier.
        #"  Generated from:
        #"      Lu + Ll + Lt + Lm + Lo + Nl
        #"    + Other_ID_Start
        #"    - Pattern_Syntax
        #"    - Pattern_White_Space
        #"  NOTE: See UAX #31 for more information

        return (
            (
                cat in ['Lu', 'Ll', 'Lt', 'Lm', 'Lo', 'Nl']
                or
                pychar in ucp.Other_ID_Start
            )
            and
            not pychar in ucp.Pattern_Syntax
            and
            not pychar in ucp.Pattern_White_Space
        )

    elif property_name == 'ID_Continue':
        # https://www.unicode.org/Public/UCD/latest/ucd/DerivedCoreProperties.txt:
        #
        #" Derived Property: ID_Continue
        #"  Characters that can continue an identifier.
        #"  Generated from:
        #"      ID_Start
        #"    + Mn + Mc + Nd + Pc
        #"    + Other_ID_Continue
        #"    - Pattern_Syntax
        #"    - Pattern_White_Space
        #"  NOTE: See UAX #31 for more information

        return (
            (
                unicode_character_has_property(pychar, 'ID_Start')
                or
                cat in ['Mn', 'Mc', 'Nd', 'Pc']
                or
                pychar in ucp.Other_ID_Continue
            )
            and
            not pychar in ucp.Pattern_Syntax
            and
            not pychar in ucp.Pattern_White_Space
        )

    else:
        assert 0, property_name

# http://www.unicode.org/reports/tr44/ says:
#" Implementations should simply use the derived properties,
#" and should not try to rederive them
#" from lists of simple properties and collections of rules,
#" because of the chances for error and divergence when doing so.
#
# E.g., Rather than the code above, I should scan
# https://www.unicode.org/Public/UCD/latest/ucd/DerivedCoreProperties.txt
# to find out all the characters with property ID_Start.
#
# However,
# (a) ID_Start has 131482 code points and ID_Continue has 134434,
#     so I'd rather not. 
# (b) The formulae are more likely to be correct wrt future versions of Unicode.
#     I.e. Python's 'unicodedata' module will be updated.

# ------------------------------------------------------------------------------
# a sequence of code points

@dataclass(frozen=True)
class ES_UnicodeCodePoints(ES_Value):
    text: str

    def number_of_code_points(self):
        return len(self.text)

    def code_points(self):
        return [
            ES_UnicodeCodePoint(ord(char))
            for char in self.text
        ]

    def each(self, item_nature_s):
        assert item_nature_s == 'code point'
        return self.code_points()

    def replace_backslashUniEscapeSeqs(self):
        if '\\' in self.text:
            def replfunc(mo):
                hexdigits = mo.group(1) or mo.group(2)
                return chr(int(hexdigits,16))
            unescaped_text = re.sub(r'\\u{([\da-fA-F]+)}|\\u([\da-fA-F]{4})', replfunc, self.text)
            return ES_UnicodeCodePoints(unescaped_text)
        else:
            return self

    def contains_code_point(self, code_point):
        assert code_point.isan(ES_UnicodeCodePoint)
        return chr(code_point.scalar) in self.text

    def contains_any_code_points_other_than(self, allowed_code_points):
        return any(
            ES_UnicodeCodePoint(ord(char)) not in allowed_code_points
            for char in self.text
        )

    def contains_the_same_code_point_more_than_once(self):
        return (len(set(list(self.text))) < len(self.text))

# -----------

@P("{VAL_DESC} : ECMAScript source text")
@P("{VAL_DESC} : source text")
@P("{VAL_DESC} : a sequence of Unicode code points")
class _:
    s_tb = T_Unicode_code_points_

@P("{LITERAL} : {backticked_oth}")
class _:
    s_tb = a_subset_of(T_Unicode_code_points_)

    def s_expr(expr, env0, _):
        [_] = expr.children
        return (T_Unicode_code_points_, env0)

# -----------
# expressions that return a sequence of Unicode code points:

@P("{EXPR} : the empty sequence of Unicode code points")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_Unicode_code_points_, env0)

@P("{LITERAL} : {backticked_word}")
class _:
    def s_tb(expr, env):
        [backticked_word] = expr.children
        word = backticked_word.source_text()[1:-1]
        assert word in ['super', 'this']
        return a_subset_of(T_grammar_symbol_)

    def s_expr(expr, env0, _):
        [backticked_word] = expr.children
        word = backticked_word.source_text()[1:-1]
        if word == 'General_Category':
            return (T_Unicode_code_points_, env0)
        elif word in ['u', 'v']:
            return (T_code_point_, env0)
        else:
            assert 0, word

    d_exec = d_exec_pass_down

@P(r"{backticked_word} : ` \w+ `")
class _:
    def d_exec(backticked_word):
        [chars] = backticked_word.children
        word_chars = chars[1:-1]
        return ES_UnicodeCodePoints(word_chars)

@P("{EXPR} : the List of Unicode code points {var}")
class _:
    def s_expr(expr, env0, _):
        [v] = expr.children
        env0.assert_expr_is_of_type(v, ListType(T_code_point_))
        return (ListType(T_code_point_), env0)

# -------------------------------------------------------
# conditions involving a sequence of Unicode code points:

@P("{CONDITION_1} : {EX} contains any code point more than once")
class _:
    def s_cond(cond, env0, asserting):
        [noi] = cond.children
        env0.assert_expr_is_of_type(noi, T_Unicode_code_points_)
        return (env0, env0)

    def d_exec(cond):
        [var] = cond.children
        code_points = EXEC(var, ES_UnicodeCodePoints)
        return code_points.contains_the_same_code_point_more_than_once()

@P("{CONDITION_1} : {EX} contains any code points other than {backticked_word}, {backticked_word}, {backticked_word}, {backticked_word}, {backticked_word}, {backticked_word}, {backticked_word}, or {backticked_word}")
class _:
    def s_cond(cond, env0, asserting):
        [noi, *bw_] = cond.children
        env0.assert_expr_is_of_type(noi, T_Unicode_code_points_)
        for bw in bw_:
            assert len(bw.source_text()) == 3 # single-character 'words'
        return (env0, env0)

    def d_exec(cond):
        [var, *backticked_words] = cond.children
        code_points = EXEC(var, ES_UnicodeCodePoints)
        allowed_code_points = []
        for btw in backticked_words:
            cps = EXEC(btw, ES_UnicodeCodePoints)
            assert cps.number_of_code_points() == 1
            [cp] = cps.code_points()
            allowed_code_points.append(cp)
        return code_points.contains_any_code_points_other_than(allowed_code_points)

# ==============================================================================
# code unit

# (We can infer that it means "a UTF-16 code unit value".)

@dataclass(frozen=True)
class ES_CodeUnit(E_Value):
    numeric_value: int
    # Note that it's a Python integer rather than an ES_Mathnum.
    # This might cause problems later.

    def __init__(self, numeric_value):
        assert isinstance(numeric_value, int)
        assert 0 <= numeric_value < 2 ** 16
        object.__setattr__(self, 'numeric_value', numeric_value)

@P("{VAL_DESC} : a UTF-16 code unit")
@P("{VAL_DESC} : a code unit")
class _:
    s_tb = T_code_unit_

@P('{VAL_DESC} : a leading surrogate')
@P('{VAL_DESC} : a trailing surrogate')
class _:
    def s_tb(val_desc, env):
        return a_subset_of(T_code_unit_)

# ----
# Expressions that return a code unit:

@P("{LITERAL} : {code_unit_lit}")
class _:
    s_tb = a_subset_of(T_code_unit_)
    s_expr = s_expr_pass_down
    d_exec = d_exec_pass_down

@P(r"{code_unit_lit} : \b 0x [0-9A-F]{4} \x20 \( [A-Z -]+ \)")
@P(r"{code_unit_lit} : the \x20 code \x20 unit \x20 0x [0-9A-F]{4} \x20 \( [A-Z -]+ \)")
class _:
    def s_expr(expr, env0, _):
        return (T_code_unit_, env0)

    def d_exec(code_unit_lit):
        [chars] = code_unit_lit.children
        mo = re.fullmatch(r'the code unit 0x([0-9A-F]{4}) \([A-Z -]+\)', chars)
        assert mo
        cu_hex = mo.group(1)
        cu_int = int(cu_hex, 16)
        return ES_CodeUnit(cu_int)

@P("{EX} : the code unit whose numeric value is {EX}")
class _:
    def s_expr(expr, env0, _):
        [ex] = expr.children
        env0.assert_expr_is_of_type(ex, T_MathNonNegativeInteger_)
        return (T_code_unit_, env0)

    def d_exec(expr):
        [ex] = expr.children
        m = EXEC(ex, ES_Mathnum)
        return ES_CodeUnit(m.val)

@P("{EX} : the code unit whose numeric value is determined by {PROD_REF} according to {h_emu_xref}")
class _:
    def s_expr(expr, env0, _):
        [prod_ref, emu_xref] = expr.children
        env0.assert_expr_is_of_type(prod_ref, T_Parse_Node)
        return (T_code_unit_, env0)

    def d_exec(expr):
        [prod_ref, emu_xref] = expr.children
        pnode = EXEC(prod_ref, ES_ParseNode)
        assert pnode.symbol == 'SingleEscapeCharacter'
        pnode_text = pnode.text()
        assert len(pnode_text) == 1
        escape_seq = '\\' + pnode_text

        emu_table = dereference_emu_xref(emu_xref)
        assert emu_table.element_name == 'emu-table'
        assert emu_table.attrs['caption'] == 'String Single Character Escape Sequences'
        row = emu_table_get_unique_row_satisfying(emu_table, lambda row: row.as_dict['Escape Sequence'] == escape_seq)
        cu_hex = row.as_dict['Code Unit Value']
        cu_int = int(cu_hex, 16)
        return ES_CodeUnit(cu_int)

# ==============================================================================
# code point and/or code unit

@P("{NUM_COMPARAND} : the numeric value of {var}")
@P("{EX} : the numeric value of {EX}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        # polymorphic
        env1 = env0.ensure_expr_is_of_type(var, T_code_unit_ | T_code_point_)
        return (T_MathInteger_, env1)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 4 Overview

# ==============================================================================
#@ 4.2 Hosts and Implementations

@P("{CONDITION_1} : the host is a web browser")
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

# --------------
# grammar symbol

class ES_GrammarSymbol(ES_Value): pass

@P("{VAL_DESC} : a grammar symbol")
class _:
    s_tb = T_grammar_symbol_

# -------------------
# nonterminal symbols

@dataclass(frozen=True)
class ES_NonterminalSymbol(ES_GrammarSymbol):
    name: str

@P(r"{nonterminal} : \| [A-Za-z][A-Za-z0-9]* \?? (\[ .+? \])? \|")
class _:
    def s_expr(expr, env0, _):
        nont_name = expr.source_text()[1:-1]
        # Note that |Foo| often denotes a Parse Node,
        # rather than a grammar symbol,
        # but we capture those cases before they can get to here.
        return (T_grammar_symbol_, env0)

    def d_exec(nonterminal):
        [chars] = nonterminal.children
        return ES_NonterminalSymbol(chars[1:-1])

def nt_name_from_nonterminal_node(nonterminal_node):
    assert isinstance(nonterminal_node, ANode)
    nonterminal_node.prod.lhs_s == 'nonterminal'
    [nonterminal_str] = nonterminal_node.children
    mo = re.fullmatch(r'\|(\w+)(\[[+~\w, ]+\])?\|', nonterminal_str)
    return mo.group(1)

@P("{VAL_DESC} : a nonterminal in one of the ECMAScript grammars")
class _:
    s_tb = a_subset_of(T_grammar_symbol_)

@P("{EXPR} : the grammar symbol {nonterminal}")
class _:
    def s_expr(expr, env0, _):
        [nont] = expr.children
        return (T_grammar_symbol_, env0)

@P("{G_SYM} : {nonterminal}")
class _:
    def s_expr(expr, env0, _):
        return (T_grammar_symbol_, env0)

    def d_exec(g_sym):
        [nonterminal] = g_sym.children
        [nont_str] = nonterminal.children
        assert nont_str.startswith('|')
        assert nont_str.endswith('|')
        return ES_NonterminalSymbol(nont_str[1:-1])

@P("{VAL_DESC} : {nonterminal}")
class _:
    def s_tb(val_desc, env):
        [nont] = val_desc.children
        return a_subset_of(T_grammar_symbol_)

    def d_desc(val_desc, value):
        [nonterminal] = val_desc.children
        nt_name = nt_name_from_nonterminal_node(nonterminal)

        assert value.isan(ES_GrammarSymbol)
        return (
            value.isan(ES_NonterminalSymbol)
            and
            value.name == nt_name
        )

# ----------------
# terminal symbols

@dataclass(frozen=True)
class ES_TerminalSymbol(ES_GrammarSymbol):
    chars: str

    @staticmethod
    def from_TERMINAL_anode(terminal):
        assert isinstance(terminal, ANode)
        assert terminal.prod.lhs_s == '{TERMINAL}'
        backticked_str = terminal.source_text()
        assert backticked_str.startswith('`')
        assert backticked_str.endswith('`')
        return ES_TerminalSymbol(backticked_str[1:-1])

@P("{G_SYM} : {TERMINAL}")
class _:
    def s_expr(expr, env0, _):
        return (T_grammar_symbol_, env0)

    def d_exec(g_sym):
        [terminal] = g_sym.children
        return ES_TerminalSymbol.from_TERMINAL_anode(terminal)

@P("{LITERAL} : the {nonterminal} {TERMINAL}")
class _:
    def s_tb(literal, env):
        [nont, term] = literal.children
        assert nont.source_text() == '|ReservedWord|'
        assert term.source_text() == "`super`"
        return a_subset_of(T_grammar_symbol_)

    def s_expr(expr, env0, _):
        return (T_grammar_symbol_, env0)

    def d_exec(literal):
        [nont, term] = literal.children
        assert nont.source_text() == '|ReservedWord|'
        assert term.source_text() == "`super`"
        return ES_TerminalSymbol.from_TERMINAL_anode(term)

# ==============================================================================
#@ 5.1.2 The Lexical and RegExp Grammars

def pychar_matches_lexical_nonterminal(pychar, nt_name):
    g = spec.grammar_[('lexical', 'A')]
    for rhs in g.prodn_for_lhs_[nt_name]._rhss:
        if pychar_matches_rhs(pychar, rhs):
            return True
    return False

def pychar_matches_rhs(pychar, rhs):
    assert rhs.kind == 'RHS_LINE'
    assert len(rhs._rhs_items) == 1
    [r_item] = rhs._rhs_items

    if r_item.kind == 'GNT':
        assert not r_item._is_optional
        assert r_item._params == []
        return pychar_matches_lexical_nonterminal(pychar, r_item._nt_name)

    elif r_item.kind == 'BACKTICKED_THING':
        return (pychar == r_item._chars)

    elif r_item.kind == 'U_PROP':
        [unicode_property_name] = r_item.groups
        return unicode_character_has_property(pychar, unicode_property_name)

    elif r_item.kind == 'NAMED_CHAR':
        [char_name] = r_item.groups
        named_pychar = {
            'ZWNJ'  : '\u200c',
            'ZWJ'   : '\u200d',
        }[char_name]
        return (pychar == named_pychar)

    else:
        assert NYI, r_item.kind

# ==============================================================================
#@ 5.1.3 The Numeric String Grammar

# ==============================================================================
#@ 5.1.4 The Syntactic Grammar

#> It defines a set of productions,
#> starting from two alternative goal symbols |Script| and |Module|, ...

@P("{CONDITION_1} : the goal symbol of the syntactic grammar is {nonterminal}")
class _:
    def s_cond(cond, env0, asserting):
        [nont] = cond.children
        return (env0, env0)

    def d_exec(cond):
        [nont] = cond.children
        nt_name = nt_name_from_nonterminal_node(nont)
        assert nt_name in ['Script', 'Module']

        pnode = curr_frame()._focus_node
        while True:
            if pnode.parent:
                pnode = pnode.parent
            elif hasattr(pnode, 'covering_thing'):
                pnode = pnode.covering_thing
            else:
                break
        assert pnode.parent is None

        assert pnode.symbol in ['Script', 'Module']
        return (pnode.symbol == nt_name)

@P("{CONDITION_1} : the syntactic goal symbol is not {nonterminal}")
class _:
    def s_cond(cond, env0, asserting):
        [nont] = cond.children
        return (env0, env0)

# ------------------------------------------------------------------------------
#> When a parse is successful, it constructs a parse tree,
#> a rooted tree structure in which each node is a <dfn>Parse Node</dfn>.

class ES_AbsentParseNode(ES_Value): pass

@P("{VAL_DESC} : a Parse Node")
@P("{LIST_ELEMENTS_DESCRIPTION} : Parse Nodes")
class _:
    s_tb = T_Parse_Node

    def d_desc(val_desc, value):
        [] = val_desc.children
        return value.isan(ES_ParseNode)

# ------------------------------------------------------------------------------
#> Each Parse Node is an <em>instance</em> of a symbol in the grammar;

# -----
# explicit "instance of symbol":

@P("{VAL_DESC} : an instance of a nonterminal")
class _:
    s_tb = a_subset_of(T_Parse_Node)

    def d_desc(val_desc, value):
        [] = val_desc.children
        assert value.isan(ES_ParseNode) # or that might be part of the test
        return not value.is_terminal

@P("{VAL_DESC} : an instance of {var}")
class _:
    def s_tb(val_desc, env):
        [var] = val_desc.children
        env.assert_expr_is_of_type(var, T_grammar_symbol_)
        return a_subset_of(T_Parse_Node)

    def d_desc(val_desc, value):
        [var] = val_desc.children
        gsym = EXEC(var, ES_GrammarSymbol)
        if gsym.isan(ES_TerminalSymbol):
            desired_node_symbol = T_lit(gsym.chars)
            # Theoretically, it could be a different kind of T_foo,
            # but so far, the only case of this is `super`.
        elif gsym.isan(ES_NonterminalSymbol):
            desired_node_symbol = gsym.name
        else:
            assert 0
        assert value.isan(ES_ParseNode) # or that might be part of the test
        return value.symbol == desired_node_symbol

# -----
# implicit "[instance of] symbol": (should the spec make it explicit?)

@P("{VAL_DESC} : an? {nonterminal}")
@P("{VAL_DESC} : an? {nonterminal} Parse Node")
@P("{LIST_ELEMENTS_DESCRIPTION} : {nonterminal} Parse Nodes")
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

    def d_desc(val_desc, value):
        [nonterminal] = val_desc.children
        nt_name = nt_name_from_nonterminal_node(nonterminal)
        if nt_name == 'ReservedWord':
            # The wording suggests that it's asking whether
            # a Parse Node is an instance of some nonterminal,
            # but it's actually asking
            # whether a String value conforms to the syntax of |ReservedWord|.
            # This question is a bit odd,
            # because |ReservedWord| (like all grammar symbols)
            # defines a syntax for Unicode text, not strings.
            # However, |ReservedWord| only involves Latin letters,
            # so ...

            assert value.isan(EL_String)
        
            # kludge

            if value in [
                EL_String.from_Python_string('a'),
                EL_String.from_Python_string('b'),
            ]:
                return False

            assert NYI

        else:
            # Here, {value} is a Parse Node,
            # and we're asking if it's an instance of the given nonterminal.
            # Or sometimes, we're asking if it *contains* such a node via one or more unit rules.

            # As an example of the latter, consider:
            # `If |LeftHandSideExpression| is an |ObjectLiteral| or an |ArrayLiteral|, ...`
            # A |LeftHandSideExpression| Parse Node can't literally be
            # an |ObjectLiteral| Parse Node or an |ArrayLiteral| Parse Node.
            # Rather, the question is whether the |LeftHandSideExpression|
            # can unit-derive an |ObjectLiteral| Parse Node or an |ArrayLiteral| Parse Node.

            assert value.isan(ES_ParseNode)
            d = value.unit_derives_a(nt_name)
            # via *zero* or more unit rules, so covers both meanings.

            if d is None:
                return False
            else:
                if d is not value:
                    # {value} itself is not an {nt_name},
                    # but a descendant of it, {d}, is.
                    # I.e. the test is true only under the "contains" interpretation.
                    # So we assume that that's what was intended. 
                    vdst = val_desc.source_text()
                    assert vdst in [
                        'an |ArrayLiteral|',
                        'an |ObjectLiteral|',
                        # in numerous scattered occurrences of
                        # `is either an |ObjectLiteral| or an |ArrayLiteral|` and
                        # `is neither an |ObjectLiteral| nor an |ArrayLiteral|`

                        'a |LabelledStatement|', # in IsLabelledFunction
                    ]

                    # kludge for IsLabelledFunction:
                    if vdst == 'a |LabelledStatement|':
                        cc_cond = val_desc.closest_containing('{CONDITION_1}')
                        assert cc_cond.source_text() == "_stmt_ is not a |LabelledStatement|"

                        varname = '_stmt_'
                        contour = curr_frame()._contours[0]
                        assert varname in contour

                        stmt = contour[varname]
                        assert stmt.symbol == 'Statement'

                        # I.e., _stmt_ is actually a |Statement| Parse Node
                        # (as IsLabelledFunction's parameter list states),
                        # but the condition has just said that it's a |LabelledStatement|,
                        # which really means that it unit-derives {d} which is a |LabelledStatement|.

                        # The thing is, the next step in IsLabelledFunction says:
                        #     1. Let _item_ be the |LabelledItem| of _stmt_.
                        # which assumes that _stmt_ now refers to the |LabelledStatement| {d}.
                        # So we accomplish that here:
                        contour[varname] = d

                return True

# 13.2.3.1
@P("{CONDITION_1} : {PROD_REF} is the token `false`")
@P("{CONDITION_1} : {PROD_REF} is the token `true`")
class _:
    def s_cond(cond, env0, asserting):
        [prod_ref] = cond.children
        assert prod_ref.source_text() == '|BooleanLiteral|'
        env0.assert_expr_is_of_type(prod_ref, T_Parse_Node)
        return (env0, env0)

# ------------------------------------------------------------------------------
#> [Each Parse Node, an instance of a symbol,]
#> represents a span of the source text that can be derived from that symbol.

# (from 5.2.2 Syntax-Directed Operations)
#> The <dfn>source text matched by</dfn> a grammar production
#> or Parse Node derived from it
#> is the portion of the source text
#> that starts at the beginning of the first terminal that participated in the match
#> and ends at the end of the last terminal that participated in the match.

@P("{EXPR} : the source text that was recognized as {PROD_REF}")
class _:
    def s_expr(expr, env0, _):
        [prod_ref] = expr.children
        env0.assert_expr_is_of_type(prod_ref, T_Parse_Node)
        return (T_Unicode_code_points_, env0)

    def d_exec(expr):
        [prod_ref] = expr.children
        node = EXEC(prod_ref, ES_ParseNode)
        return ES_UnicodeCodePoints(node.text())

@P("{EX} : the source text matched by {PROD_REF}")
class _:
    def s_expr(expr, env0, _):
        [prod_ref] = expr.children
        env0.assert_expr_is_of_type(prod_ref, T_Parse_Node)
        return (T_Unicode_code_points_, env0) # XXX spec bug: needs to be T_String?

@P("{EX} : the code point matched by {PROD_REF}")
class _:
    def s_expr(expr, env0, _):
        [prod_ref] = expr.children
        env0.assert_expr_is_of_type(prod_ref, T_Parse_Node)
        return (T_code_point_, env0)

    def d_exec(expr):
        [prod_ref] = expr.children
        pnode = EXEC(prod_ref, ES_ParseNode)
        t = pnode.text()
        assert len(t) == 1
        return ES_UnicodeCodePoint(ord(t))

@P("{EX} : the single code point matched by this production")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_code_point_, env0)

@P("{EX} : the number of code points in {PROD_REF}")
# SPEC BUG: should be "the number of code points in *the source text matched by* {PROD_REF}"
class _:
    def s_expr(expr, env0, _):
        [prod_ref] = expr.children
        env0.assert_expr_is_of_type(prod_ref, T_Parse_Node)
        return (T_MathNonNegativeInteger_, env0)

    def d_exec(expr):
        [prod_ref] = expr.children
        pnode = EXEC(prod_ref, ES_ParseNode)
        return ES_Mathnum(len(pnode.text()))

@P("{EX} : the number of code points in {PROD_REF}, excluding all occurrences of {nonterminal}")
class _:
    def s_expr(expr, env0, _):
        [prod_ref, nont] = expr.children
        env0.assert_expr_is_of_type(prod_ref, T_Parse_Node)
        return (T_MathNonNegativeInteger_, env0)

    def d_exec(expr):
        [prod_ref, nont] = expr.children
        pnode = EXEC(prod_ref, ES_ParseNode)
        assert nont.source_text() == '|NumericLiteralSeparator|'
        return ES_Mathnum(len(pnode.text().replace('_', '')))

@P("{CONDITION_1} : any source text is matched by this production")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

    def d_exec(cond):
        [] = cond.children
        return True

# ------------------------------------------------------------------------------
#> When a Parse Node is an instance of a nonterminal,
#> it is also an instance of some production
#> that has that nonterminal as its left-hand side.

# explicit "instance of production":

@P("{VAL_DESC} : an instance of a production in {h_emu_xref}")
class _:
    s_tb = a_subset_of(T_Parse_Node)

    def d_desc(val_desc, value):
        [emu_xref] = val_desc.children
        emu_clause = dereference_emu_xref(emu_xref)
        assert emu_clause.element_name == 'emu-clause'
        lhs_symbols = set()
        for emu_grammar in emu_clause.each_descendant_named('emu-grammar'):
            if emu_grammar.attrs.get('type', 'ref') == 'definition':
                for production_n in emu_grammar._gnode._productions:
                    lhs_symbols.add(production_n._lhs_symbol)

        assert value.isan(ES_ParseNode)
        return value.symbol in lhs_symbols

@P("{VAL_DESC} : an instance of the production {h_emu_grammar}")
class _:
    def s_tb(val_desc, env):
        [emu_grammar] = val_desc.children
        emu_grammar_text = emu_grammar.source_text()
        lhs = re.sub(r'<emu-grammar>(\w+) :.*', r'\1', emu_grammar_text)
        prodn_type = ptn_type_for(lhs)
        return a_subset_of(prodn_type)

@P("{EXPR} : an instance of the production {h_emu_grammar}")
class _:
    def s_expr(expr, env0, _):
        [emu_grammar] = expr.children
        assert emu_grammar.source_text() == '<emu-grammar>FormalParameters : [empty]</emu-grammar>'
        return (ptn_type_for('FormalParameters'), env0)

# implicit "[instance of] production": (should the spec make it explicit?)

@P("{CONDITION_1} : {LOCAL_REF} is {h_emu_grammar}")
class _:
    def s_cond(cond, env0, asserting):
        [local_ref, h_emu_grammar] = cond.children
        env0.assert_expr_is_of_type(local_ref, T_Parse_Node)
        env1 = env0.copy()
        env1.assoc_productions = h_emu_grammar._hnode._gnode._productions
        return (env1, env0)

    def d_exec(cond):
        [local_ref, h_emu_grammar] = cond.children
        pnode = EXEC(local_ref, ES_ParseNode)
        result = (pnode.puk in h_emu_grammar._hnode.puk_set)

        # But this can also augment the current focus_map.
        if hasattr(curr_frame(), 'focus_map'):
            # E.g., in TopLevelVarDeclaredNames,
            #> StatementListItem : Declaration
            #>    1. If |Declaration| is |Declaration : HoistableDeclaration|, then
            #>       a. Return the BoundNames of |HoistableDeclaration|.
            curr_frame().augment_focus_map(pnode)
        else:
            # E.g., in IsLabelledFunction, 
            #>    1. If _item_ is <emu-grammar>LabelledItem : FunctionDeclaration</emu-grammar>, return *true*.
            # Conceivably, it could *create* a focus_map?
            # We'll assume it doesn't, and see what happens.
            pass

        return result

@P("{CONDITION_1} : {LOCAL_REF} is {h_emu_grammar}, {h_emu_grammar}, {h_emu_grammar}, {h_emu_grammar}, or {h_emu_grammar}")
class _:
    def s_cond(cond, env0, asserting):
        [local_ref, *h_emu_grammar_] = cond.children
        env0.assert_expr_is_of_type(local_ref, T_Parse_Node)
        return (env0, env0)

    def d_exec(cond):
        [local_ref, *h_emu_grammar_] = cond.children
        pnode = EXEC(local_ref, ES_ParseNode)
        result = any(
            pnode_unit_derives_a_node_with_puk(pnode, h_emu_grammar._hnode.puk_set)
            for h_emu_grammar in h_emu_grammar_
        )
        return result

def pnode_unit_derives_a_node_with_puk(pnode, puk_arg):
    # (Make this a ES_ParseNode method?)
    if isinstance(puk_arg, set):
        puk_set = puk_arg
    elif isinstance(puk_arg, tuple):
        puk_set = set([puk_arg])
    else:
        assert 0, puk_arg

    descendant = pnode
    while True:
        if descendant.is_terminal:
            return None
        if descendant.puk in puk_set:
            return descendant
        if len(descendant.children) != 1:
            return None
        [descendant] = descendant.children

@P("{CONDITION_1} : {PROD_REF} is `export` {nonterminal}")
class _:
    def s_cond(cond, env0, asserting):
        [prod_ref, nont] = cond.children
        env0.assert_expr_is_of_type(prod_ref, T_Parse_Node)
        return (env0, env0)

    def d_exec(cond):
        [prod_ref, nont] = cond.children
        nt_name = nt_name_from_nonterminal_node(nont)
        pnode = EXEC(prod_ref, ES_ParseNode)
        return (
            len(pnode.children) == 2
            and
            pnode.children[0].symbol == T_lit('export')
            and
            pnode.children[1].symbol == nt_name
        )

# ------------------------------------------------------------------------------
#> Moreover, it has zero or more <em>children</em>,
#> one for each symbol on the production's right-hand side:
#> each child is a Parse Node that is an instance of the corresponding symbol.

@P("{EACH_THING} : child node {DEFVAR} of this Parse Node")
class _:
    def s_nv(each_thing, env0):
        [loop_var] = each_thing.children
        env1 = env0.plus_new_entry(loop_var, T_Parse_Node)
        return env1

    def d_each(each_thing):
        [defvar] = each_thing.children
        pnode = curr_frame()._focus_node
        # return (var, pnode.children)
        #
        # optimization:
        # Don't cross the syntactic/lexical boundary.
        #
        # (Prompted by pass/0b1fc7208759253b.js,
        # which caused a segfault, presumably from a too-deep stack.
        # Could have increased the recursionlimit, but why bother?)
        same_tip_children = [
            child_node
            for child_node in pnode.children
            if child_node.tip is pnode.tip
        ]
        return (defvar, same_tip_children)

# (You can refer to a particular child of X by saying "the {nonterminal} of X".)

@P("{PROD_REF} : the {nonterminal} of {LOCAL_REF}")
class _:
    def s_expr(expr, env0, _):
        [nonterminal, var] = expr.children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        # XXX should get more precise type for {var} and check that it could have a child of that kind
        return (ptn_type_for(nonterminal), env0)

    def d_exec(expr):
        [nonterminal, local_ref] = expr.children
        nt_name = nt_name_from_nonterminal_node(nonterminal)
        pnode = EXEC(local_ref, ES_ParseNode)
        selected_children = [
            child
            for child in pnode.children
            if child.symbol == nt_name
        ]
        assert len(selected_children) == 1
        [selected_child] = selected_children
        return selected_child

@P("{VAL_DESC} : the {nonterminal} of an? {nonterminal}")
class _:
    def s_tb(val_desc, env):
        [nont1, nont2] = val_desc.children
        return a_subset_of(ptn_type_for(nont1))

# ------------------------------------------------------------------------------
# (A Parse Node 'contains' its children and their children, and so on)

@P("{CONDITION_1} : {EX} contains a {nonterminal}")
@P("{CONDITION_1} : {EX} contains an? {nonterminal} Parse Node")
@P("{CONDITION_1} : {var} does not contain an? {nonterminal} Parse Node")
@P("{CONDITION_1} : {var} does not contain two {nonterminal} Parse Nodes")
class _:
    def s_cond(cond, env0, asserting):
        [var, nont] = cond.children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        env0.assert_expr_is_of_type(nont, T_grammar_symbol_)
        return (env0, env0)

    def d_exec(cond):
        [var, nont] = cond.children
        pnode = EXEC(var, ES_ParseNode)
        nt_name = nt_name_from_nonterminal_node(nont)
        contains_it = pnode.contains_a(nt_name)
        if 'does not' in cond.prod.rhs_s:
            return not contains_it
        else:
            return contains_it

@P('{PROD_REF} : the {nonterminal} Parse Node contained within {var}')
class _:
    def s_expr(expr, env0, _):
        [nonterminal, var] = expr.children
        env0.assert_expr_is_of_type(nonterminal, T_grammar_symbol_)
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        return (ptn_type_for(nonterminal), env0)

@P('{PROD_REF} : the {ORDINAL} {nonterminal} Parse Node contained within {var}')
class _:
    def s_expr(expr, env0, _):
        [ordinal, nonterminal, var] = expr.children
        # ignore ordinal?
        env0.assert_expr_is_of_type(nonterminal, T_grammar_symbol_)
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        return (ptn_type_for(nonterminal), env0)

@P("{EACH_THING} : {nonterminal} {DEFVAR} that {var} contains")
class _:
    def s_nv(each_thing, env0):
        [nont, loop_var, root_var] = each_thing.children
        env0.assert_expr_is_of_type(root_var, T_Parse_Node)
        return env0.plus_new_entry(loop_var, ptn_type_for(nont))

@P("{EXPR} : the number of {h_emu_grammar} Parse Nodes contained within {var}")
class _:
    def s_expr(expr, env0, _):
        [emu_grammar, root_var] = expr.children
        env0.assert_expr_is_of_type(root_var, T_Parse_Node)
        return (T_MathNonNegativeInteger_, env0)

    def d_exec(expr):
        [emu_grammar, pnode_var] = expr.children
        puk_set = emu_grammar._hnode.puk_set
        pnode = EXEC(pnode_var, ES_ParseNode)
        count = 0
        for descendant in pnode.preorder_traverse():
            if not descendant.is_terminal and descendant.puk in puk_set:
                count += 1
        return ES_Mathnum(count)

@P("{EXPR} : the number of {h_emu_grammar} Parse Nodes contained within {var} that either occur before {var} or contain {var}")
class _:
    def s_expr(expr, env0, _):
        [emu_grammar, root_var, x_var, x_var2] = expr.children
        env0.assert_expr_is_of_type(root_var, T_Parse_Node)
        env0.assert_expr_is_of_type(x_var, T_Parse_Node)
        assert x_var.source_text() == x_var2.source_text()
        return (T_MathNonNegativeInteger_, env0)

@P("{CONDITION_1} : {EX} contains two or more {nonterminal}s for which {NAMED_OPERATION_INVOCATION} is the same")
class _:
    def s_cond(cond, env0, asserting):
        [ex, nonta, noi] = cond.children
        env0.assert_expr_is_of_type(ex, T_Parse_Node)
        # XXX noi
        return (env0, env0)

    def d_exec(cond):
        [local_ref, nont, noi] = cond.children
        pnode = EXEC(local_ref, ES_ParseNode)
        nt_name = nt_name_from_nonterminal_node(nont)
        vals = set()
        for descendant in pnode.preorder_traverse():
            if descendant.symbol == nt_name:
                val = EXEC(noi, E_Value)
                if val in vals: return True
                vals.add(val)
        return False

# ------------------------------------------------------------------------------
# (You can ask about nodes that contain _P_)

@P("{PROD_REF} : the {nonterminal} containing {LOCAL_REF}")
class _:
    def s_expr(expr, env0, _):
        [nonta, local_ref] = expr.children
        env0.assert_expr_is_of_type(local_ref, T_Parse_Node)
        return (T_Parse_Node, env0)

    def d_exec(expr):
        [container_nont, local_ref] = expr.children
        container_nt = nt_name_from_nonterminal_node(container_nont)
        pnode = EXEC(local_ref, ES_ParseNode)
        containers = [
            anc
            for anc in pnode.each_ancestor()
            if anc.symbol == container_nt
        ]
        assert len(containers) == 1
        return containers[0]

@P("{EXPR} : the {nonterminal}, {nonterminal}, or {nonterminal} that most closely contains {var}")
class _:
    def s_expr(expr, env0, _):
        [*nont_, var] = expr.children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        return (T_Parse_Node, env0)

@P("{CONDITION_1} : {var} is not contained within an? {nonterminal}, an? {nonterminal}, or an? {nonterminal}")
class _:
    def s_cond(cond, env0, asserting):
        [var, *nont_] = cond.children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        return (env0, env0)

# ------------------------------------------------------------------------------
# (A Parse Node is 'nested' within its ancestor nodes.)

@P("{CONDITION_1} : {LOCAL_REF} is not nested, directly or indirectly (but not crossing function or `static` initialization block boundaries), within an {nonterminal}")
class _:
    def s_cond(cond, env0, asserting):
        [local_ref, nont] = cond.children
        env0.assert_expr_is_of_type(local_ref, T_Parse_Node)
        return (env0, env0)

    def d_exec(cond):
        [local_ref, nont] = cond.children
        nt_name = nt_name_from_nonterminal_node(nont)
        pnode = EXEC(local_ref, ES_ParseNode)
        return not node_is_nested_but_not_crossing_function_boundaries_within_a(pnode, [nt_name])

@P("{CONDITION_1} : {LOCAL_REF} is not nested, directly or indirectly (but not crossing function or `static` initialization block boundaries), within an {nonterminal} or a {nonterminal}")
class _:
    def s_cond(cond, env0, asserting):
        [local_ref, nonta, nontb] = cond.children
        env0.assert_expr_is_of_type(local_ref, T_Parse_Node)
        return (env0, env0)

    def d_exec(cond):
        [local_ref, nonta, nontb] = cond.children
        nt_name_a = nt_name_from_nonterminal_node(nonta)
        nt_name_b = nt_name_from_nonterminal_node(nontb)
        pnode = EXEC(local_ref, ES_ParseNode)
        return not node_is_nested_but_not_crossing_function_boundaries_within_a(pnode, [nt_name_a, nt_name_b])

def node_is_nested_but_not_crossing_function_boundaries_within_a(pnode, target_symbols):
    function_boundary_symbols = [
        'FunctionDeclaration',
        'FunctionExpression',
        'GeneratorDeclaration',
        'GeneratorExpression',
        'AsyncFunctionDeclaration',
        'AsyncFunctionExpression',
        'AsyncGeneratorDeclaration',
        'AsyncGeneratorExpression',
        'MethodDefinition',
        'ArrowFunction',
        'AsyncArrowFunction',
    ]
    static_initialization_block_boundary_symbols = [
        'ClassStaticBlock',
    ]
    boundary_symbols = function_boundary_symbols + static_initialization_block_boundary_symbols

    assert not any(
        target_symbol in boundary_symbols
        for target_symbol in target_symbols
    )
    # because that would be weird

    assert pnode.symbol not in target_symbols
    # because it's unclear whether that would satisfy the wording

    for anc in pnode.each_ancestor():
        if anc.symbol in target_symbols: return True
        if anc.symbol in boundary_symbols: return False

    return False

# ------------------------------------------------------------------------------
#> Parse Nodes are considered <dfn>the same Parse Node</dfn>
#> if and only if they represent the same span of source text,
#> are instances of the same grammar symbol,
#> and resulted from the same parser invocation.

@P("{CONDITION_1} : {EX} is the same Parse Node as {EX}")
class _:
    def s_cond(cond, env0, asserting):
        [exa, exb] = cond.children
        env0.assert_expr_is_of_type(exa, T_Parse_Node)
        env0.assert_expr_is_of_type(exb, T_Parse_Node)
        return (env0, env0)

# ------------------------------------------------------------------------------
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

@P("{EE_RULE} : {LOCAL_REF} must cover an? {nonterminal}.")
class _:
    def s_nv(anode, env0):
        [local_ref, nont] = anode.children
        env0.assert_expr_is_of_type(local_ref, T_Parse_Node)
        return None

    def d_exec(rule):
        [local_ref, nont] = rule.children
        pnode = EXEC(local_ref, ES_ParseNode)
        covered_thing = the_nonterminal_that_is_covered_by_pnode(nont, pnode)
        if covered_thing:
            traverse_for_early_errors(covered_thing)
        else:
            it_is_a_syntax_error(rule)
        return None

@P('{EE_RULE} : If {CONDITION}, {LOCAL_REF} must cover an? {nonterminal}.')
class _:
    def s_nv(anode, env0):
        [cond, local_ref, nont] = anode.children
        tc_cond(cond, env0)
        env0.assert_expr_is_of_type(local_ref, T_Parse_Node)
        return None

    def d_exec(rule):
        [cond, local_ref, nont] = rule.children
        if EXEC(cond, bool):
            pnode = EXEC(local_ref, ES_ParseNode)
            covered_thing = the_nonterminal_that_is_covered_by_pnode(nont, pnode)
            if covered_thing:
                traverse_for_early_errors(covered_thing)
            else:
                it_is_a_syntax_error(rule)
        return None

@P("{EXPR} : the {nonterminal} that is covered by {LOCAL_REF}")
class _:
    def s_expr(expr, env0, _):
        [nonterminal, local_ref] = expr.children
        env0.assert_expr_is_of_type(local_ref, T_Parse_Node)
        return (ptn_type_for(nonterminal), env0)

    def d_exec(expr):
        [nont, local_ref] = expr.children
        pnode = EXEC(local_ref, ES_ParseNode)
        covered_thing = the_nonterminal_that_is_covered_by_pnode(nont, pnode)
        if covered_thing is None:
            raise ReferenceToNonexistentThing(expr.source_text())
        return covered_thing

def the_nonterminal_that_is_covered_by_pnode(nont, pnode):
    nt_name = nt_name_from_nonterminal_node(nont)
    if hasattr(pnode, 'covered_thing'):
        pass
        # stderr('covered by:', pnode, "already has")
    else:
        ex_nt_name = nt_name + ''.join(pnode.production.og_params_setting)
        try:
            pnode.covered_thing = parse(pnode, ex_nt_name)
            # stderr('covered by:', pnode, "parse succeeded")
            assert pnode.covered_thing.symbol == nt_name
            pnode.covered_thing.covering_thing = pnode
        except ParseError:
            # stderr('covered by:', pnode, "parse failed")
            pnode.covered_thing = None
    return pnode.covered_thing

# ----------------------------------------------------------
# (this text would be matched by that nonterminal/production
# if it were source text in an appropriate context)

@P("{CONDITION_1} : {NAMED_OPERATION_INVOCATION} is not some Unicode code point matched by the {nonterminal} lexical grammar production")
class _:
    def s_cond(cond, env0, asserting):
        [noi, nont] = cond.children
        env0.assert_expr_is_of_type(noi, T_code_point_)
        return (env0, env0)

    def d_exec(cond):
        [noi, nont] = cond.children
        code_point = EXEC(noi, ES_UnicodeCodePoint)
        nt_name = nt_name_from_nonterminal_node(nont)
        return not pychar_matches_lexical_nonterminal(chr(code_point.scalar), nt_name)

@P("{CONDITION_1} : {NAMED_OPERATION_INVOCATION} is not matched by the {nonterminal} lexical grammar production")
class _:
    def s_cond(cond, env0, asserting):
        [noi, nont] = cond.children
        env0.assert_expr_is_of_type(noi, T_code_point_)
        return (env0, env0)

@P("{CONDITION_1} : {NAMED_OPERATION_INVOCATION} is not the numeric value of some code point matched by the {nonterminal} lexical grammar production")
class _:
    def s_cond(cond, env0, asserting):
        [noi, nont] = cond.children
        env0.assert_expr_is_of_type(noi, T_MathInteger_)
        return (env0, env0)

# ==============================================================================
#@ 5.1.5 Grammar Notation

# ==============================================================================
#@ 5.1.5.4 Grammatical Parameters

@P("{CONDITION_1} : {PROD_REF} has an? <sub>[{cap_word}]</sub> parameter")
@P("{CONDITION_1} : {PROD_REF} does not have an? <sub>[{cap_word}]</sub> parameter")
class _:
    def s_cond(cond, env0, asserting):
        [prod_ref, cap_word] = cond.children
        env0.assert_expr_is_of_type(prod_ref, T_Parse_Node)
        return (env0, env0)

    def d_exec(cond):
        [prod_ref, cap_word] = cond.children
        [cap_word_str] = cap_word.children
        pnode = EXEC(prod_ref, ES_ParseNode)
        has_it = (f"+{cap_word_str}" in pnode.production.og_params_setting)
        if 'does not have' in cond.prod.rhs_s:
            return not has_it
        else:
            return has_it

@P("{CONDITION_1} : the <sub>[Tagged]</sub> parameter was not set")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

    def d_exec(cond):
        [] = cond.children
        cap_word_str = 'Tagged'
        pnode = curr_frame()._focus_node
        return (f"~{cap_word_str}" in pnode.production.og_params_setting)

# ==============================================================================
#@ 5.2 Algorithm Conventions

#> The specification often uses a numbered list to specify steps in an algorithm.
#> Algorithm steps may be subdivided into sequential substeps.
#> Substeps are indented
#> and may themselves be further divided into indented substeps.

@P("{EMU_ALG_BODY} : {IND_COMMANDS}{nlai}")
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

    d_exec = d_exec_pass_down_expecting_None

@P("{COMMANDS} : {COMMANDS}{_NL_N} {COMMAND}")
class _:
    def s_nv(anode, env0):
        [commands, command] = anode.children
        env1 = tc_nonvalue(commands, env0)
        env2 = tc_nonvalue(command, env1)
        return env2

    def d_exec(anode):
        [commands, command] = anode.children
        EXEC(commands, None)
        if curr_frame().is_returning(): return
        EXEC(command, None)

# ------------------------------------------------------------------------------
#> Algorithms may be explicitly parameterized
#> with an ordered, comma-separated sequence of alias names
#> which may be used within the algorithm steps
#> to reference the argument passed in that position.

#> Optional parameters are denoted with surrounding brackets ([ , _name_ ])
#> and are no different from required parameters within algorithm steps.
# SPEC BUG: That "no different" part is incorrect for operations.
@P("{EXPR} : the number of non-optional parameters of the function definition in {h_emu_xref}")
class _:
    def s_expr(expr, env0, _):
        [xref] = expr.children
        return (T_MathNonNegativeInteger_, env0)

# ------------------------------------------------------------------------------
#> A step or substep may be written as an “if” predicate
#> that conditions its substeps.
#> In this case, the substeps are only applied if the predicate is true.
#> If a step or substep begins with the word “else”,
#> it is a predicate that is the negation of
#> the preceding “if” predicate step at the same level.

@P("{IF_CLOSED} : If {CONDITION}, {SMALL_COMMAND}. Otherwise {SMALL_COMMAND}.")
@P("{IF_CLOSED} : If {CONDITION}, {SMALL_COMMAND}. Otherwise, {SMALL_COMMAND}.")
@P("{IF_CLOSED} : If {CONDITION}, {SMALL_COMMAND}; else {SMALL_COMMAND}.")
@P("{IF_CLOSED} : If {CONDITION}, {SMALL_COMMAND}; otherwise {SMALL_COMMAND}.")
@P("{IF_CLOSED} : If {CONDITION}, {SMALL_COMMAND}; otherwise, {SMALL_COMMAND}.")
class _:
    def s_nv(anode, env0):
        [cond, t_command, f_command] = anode.children
        (t_env, f_env) = tc_cond(cond, env0)
        t_benv = tc_nonvalue(t_command, t_env)
        f_benv = tc_nonvalue(f_command, f_env)
        return env_or(t_benv, f_benv)

    def d_exec(anode):
        [cond, cmdt, cmdf] = anode.children
        if EXEC(cond, bool):
            EXEC(cmdt, None)
        else:
            EXEC(cmdf, None)

@P("{IF_CLOSED} : If {CONDITION}, {SMALL_COMMAND}; else if {CONDITION}, {SMALL_COMMAND}; else {SMALL_COMMAND}.")
class _:
    def s_nv(anode, env0):
        [cond_a, command_a, cond_b, command_b, command_c] = anode.children
        (a_t_env, a_f_env) = tc_cond(cond_a, env0)
        a_benv = tc_nonvalue(command_a, a_t_env)
        (b_t_env, b_f_env) = tc_cond(cond_b, a_f_env)
        b_benv = tc_nonvalue(command_b, b_t_env)
        c_benv = tc_nonvalue(command_c, b_f_env)
        return envs_or([a_benv, b_benv, c_benv])

@P("{IF_OTHER} : {IF_OPEN}{IF_TAIL}")
@P("{IF_TAIL} : {_NL_N} {ELSEIF_PART}{IF_TAIL}") # not used for s_nv
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

    def d_exec(anode):
        [condition_and_commands, if_tail] = anode.children
        [condition, commands] = condition_and_commands.children
        cond_value = EXEC(condition, bool)
        if cond_value:
            EXEC(commands, None)
        else:
            EXEC(if_tail, None)

@P("{IF_TAIL} : {_NL_N} {ELSE_PART}")
class _:
    def d_exec(if_tail):
        [child] = if_tail.children
        EXEC(child, None)

@P("{IF_TAIL} : {EPSILON}")
class _:
    def d_exec(if_tail):
        [] = if_tail.children
        pass

# -------------------------------------------------

@P("{EXPR} : {EX} if {CONDITION}. Otherwise, it is {EXPR}")
class _:
    def s_expr(expr, env0, _):
        [exa, cond, exb] = expr.children
        (t_env, f_env) = tc_cond(cond, env0)
        (ta, enva) = tc_expr(exa, t_env)
        (tb, envb) = tc_expr(exb, f_env)
        return (ta | tb, env_or(enva, envb))

    def d_exec(expr):
        [exa, cond, exb] = expr.children
        ex = exa if EXEC(cond, bool) else exb
        return EXEC(ex, E_Value)

# ------------------------------------------------------------------------------
#> A step may specify the iterative application of its substeps.

@P("{COMMAND} : Repeat,{IND_COMMANDS}")
class _:
    def s_nv(anode, env0):
        [commands] = anode.children

        def check_before_body(env):
            return (env, None)
            # The only way to leave a condition-less Repeat
            # is via a Return command,
            # so there can't be anything (except maybe a NOTE) after the loop.

        return tc_loop(env0, check_before_body, commands)

@P("{COMMAND} : Repeat, while {CONDITION},{IND_COMMANDS}")
@P("{COMMAND} : Repeat, until {CONDITION},{IND_COMMANDS}")
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

@P("{COMMAND} : While {CONDITION}, an implementation may perform the following steps:{IND_COMMANDS}")
class _:
    def s_nv(anode, env0):
        [cond, commands] = anode.children

        def check_before_body(env):
            (t_env, f_env) = tc_cond(cond, env)
            return (t_env, f_env)

        return tc_loop(env0, check_before_body, commands)

@P("{COMMAND} : For each {EACH_THING}, do{IND_COMMANDS}")
@P("{COMMAND} : For each {EACH_THING}, {SMALL_COMMAND}.")
class _:
    def s_nv(anode, env0):
        [each_thing, commands] = anode.children

        def check_before_body(env):
            env_for_commands  = tc_nonvalue(each_thing, env)
            return (env_for_commands, env)

        return tc_loop(env0, check_before_body, commands)

    def d_exec(anode):
        [each_thing, commands] = anode.children
        (loop_var, iterable) = EACH(each_thing)
        for value in iterable:
            curr_frame().start_contour()
            curr_frame().let_var_be_value(loop_var, value)
            EXEC(commands, None)
            curr_frame().end_contour()
            if curr_frame().is_returning(): return

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

@P("{EACH_THING} : {ITEM_NATURE} {DEFVAR} such that {CONDITION}")
@P("{EACH_THING} : {ITEM_NATURE} {DEFVAR} such that {CONDITION}, in ascending order")
@P("{EACH_THING} : {ITEM_NATURE} {DEFVAR} such that {CONDITION}, in descending order")
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
@P("{EACH_THING} : {ITEM_NATURE} {DEFVAR} of {EX}, iterating backwards from its second-to-last element")
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

        elif item_nature.prod.rhs_s == 'CharSetElement':
            item_type = T_CharSetElement
            collection_type = T_CharSet

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
                "Matcher"             : T_Matcher,
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

    def d_each(each_thing):
        [item_nature, var, ex] = each_thing.children
        item_nature_s = item_nature.source_text()
        collection = EXEC(ex, E_Value)
        if 'backwards' in each_thing.prod.rhs_s:
            assert NYI
        return (var, collection.each(item_nature_s))

@P("{CONDITION_1} : The following loop will terminate")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

# ------------------------------------------------------------------------------
#> A step that begins with “<dfn>Assert</dfn>:”
#> asserts an invariant condition of its algorithm.

@P("{COMMAND} : Assert: {CONDITION}.")
class _:
    def s_nv(anode, env0):
        [condition] = anode.children
        (t_env, f_env) = tc_cond(condition, env0, asserting=True)
        # throw away f_env
        return t_env

    def d_exec(command):
        [condition] = command.children
        cond_value = EXEC(condition, bool)
        assert cond_value is True

@P("{COMMAND} : Assert: If {CONDITION}, then {CONDITION}.")
@P("{COMMAND} : Assert: If {CONDITION}, {CONDITION}.")
class _:
    def s_nv(anode, env0):
        [cond1, cond2] = anode.children
        (t1_env, f1_env) = tc_cond(cond1, env0)
        (t2_env, f2_env) = tc_cond(cond2, t1_env, asserting=True)
        return env_or(f1_env, t2_env)

@P("{COMMAND} : Assert: {CONDITION_1} if and only if {CONDITION_1}.")
class _:
    def s_nv(anode, env0):
        [cond1, cond2] = anode.children
        (t1_env, f1_env) = tc_cond(cond1, env0)
        (t2_env, f2_env) = tc_cond(cond2, env0)
        return env_or(
            env_and(t1_env, t2_env),
            env_and(f1_env, f2_env)
        )

@P("{COMMAND} : Assert: {CONDITION_1} if {CONDITION_1}; otherwise, {CONDITION_1}.")
class _:
    def s_nv(anode, env0):
        [cond_t, cond_x, cond_f] = anode.children
        (xt_env, xf_env) = tc_cond(cond_x, env0)
        (tt_env, tf_env) = tc_cond(cond_t, xt_env, asserting=True)
        (ft_env, ff_env) = tc_cond(cond_f, xf_env, asserting=True)
        return env_or(tt_env, ft_env)

@P("{COMMAND} : Assert: {CONDITION_1}, since {CONDITION_1}.")
class _:
    def s_nv(anode, env0):
        [conda, condb] = anode.children
        (ta_env, fa_env) = tc_cond(conda, env0, asserting=True)
        (tb_env, fb_env) = tc_cond(condb, env0, asserting=True)
        return env_and(ta_env, tb_env)

# ------------------------------------------------------------------------------
#> Algorithm steps may declare named aliases for any value ...

@P(r"{var} : \b _ [A-Za-z][A-Za-z0-9]* _ \b")
class _:
    def s_expr(expr, env0, _):
        [var_name] = expr.children
        if var_name in env0.vars:
            t = env0.vars[var_name]
        else:
            add_pass_error(
                expr,
                f"{var_name} IS NOT DEFINED"
            )
            t = T_TBD
        return (t, env0)

    def d_exec(var):
        [varname] = var.children
        return curr_frame().get_value_referenced_by_var(varname)

# ------------------------------------------------------------------------------
#> ... using the form “Let _x_ be _someValue_”.

@P("{COMMAND} : Let {DEFVAR} be {EXPR}. (It may be evaluated repeatedly.)")
@P("{COMMAND} : Let {DEFVAR} be {EXPR}.")
@P("{COMMAND} : Let {DEFVAR} be {MULTILINE_EXPR}")
@P("{SMALL_COMMAND} : let {DEFVAR} be {EXPR}")
@P("{SMALL_COMMAND} : let {DEFVAR} be {EXPR}, indicating that an ordinary object should be created as the global object")
@P("{SMALL_COMMAND} : let {DEFVAR} be {EXPR}, indicating that {var}'s global `this` binding should be the global object")
class _:
    def s_nv(anode, env0):
        [var, expr] = anode.children[0:2]
        var_name = var.source_text()

        (expr_t, env1) = tc_expr(expr, env0)
        return env1.plus_new_entry(var, expr_t)

    def d_exec(command):
        [defvar, expr] = command.children
        value = EXEC(expr, E_Value)
        curr_frame().let_var_be_value(defvar, value)

@P("{COMMAND} : Let {DEFVAR} be {EXPR}. (However, if {var} = 10 and {var} contains more than 20 significant digits, every significant digit after the 20th may be replaced by a 0 digit, at the option of the implementation; and if {var} is not one of 2, 4, 8, 10, 16, or 32, then {var} may be an implementation-approximated integer representing the integer value denoted by {var} in radix-{var} notation.)")
class _:
    def s_nv(anode, env0):
        [let_var, expr, rvar, zvar, rvar2, let_var2, zvar2, rvar3] = anode.children
        assert same_source_text(let_var, let_var2)
        assert same_source_text(rvar, rvar2)
        assert same_source_text(rvar, rvar3)
        assert same_source_text(zvar, zvar2)
        (t, env1) = tc_expr(expr, env0)
        return env1.plus_new_entry(let_var, t)

@P("{COMMAND} : Let {DEFVAR} be an integer for which {NUM_EXPR} is as close to zero as possible. If there are two such {var}, pick the larger {var}.")
class _:
    def s_nv(anode, env0):
        [let_var, num_expr, var2, var3] = anode.children
        assert same_source_text(var2, let_var)
        assert same_source_text(var3, let_var)
        new_env = env0.plus_new_entry(let_var, T_MathInteger_)
        new_env.assert_expr_is_of_type(num_expr, T_MathReal_)
        return new_env

# Let {DEFVAR} and {DEFVAR} ... be ...

@P("{COMMAND} : Let {DEFVAR} and {DEFVAR} be the indirection values provided when this binding for {var} was created.")
class _:
    def s_nv(anode, env0):
        [m_var, n2_var, n_var] = anode.children
        env0.assert_expr_is_of_type(n_var, T_String)
        return env0.plus_new_entry(m_var, T_Module_Record).plus_new_entry(n2_var, T_String)

@P("{COMMAND} : Let {DEFVAR} and {DEFVAR} be integers such that {CONDITION} and for which {NUM_EXPR} is as close to zero as possible. If there are two such sets of {var} and {var}, pick the {var} and {var} for which {PRODUCT} is larger.")
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

@P("{COMMAND} : Let {DEFVAR}, {DEFVAR}, and {DEFVAR} be integers such that {CONDITION}. If there are multiple possibilities for {var}, choose the value of {var} for which {EX} is closest in value to {EX}. If there are two such possible values of {var}, choose the one that is even. Note that {var} is the number of digits in the representation of {var} using radix {var} and that {var} is not divisible by {var}.")
@P("{COMMAND} : Let {DEFVAR}, {DEFVAR}, and {DEFVAR} be integers such that {CONDITION}. Note that the decimal representation of {var} has {SUM} digits, {var} is not divisible by 10, and the least significant digit of {var} is not necessarily uniquely determined by these criteria.")
@P("{COMMAND} : Let {DEFVAR}, {DEFVAR}, and {DEFVAR} be integers such that {CONDITION}. Note that {var} is the number of digits in the representation of {var} using radix {var}, that {var} is not divisible by {var}, and that the least significant digit of {var} is not necessarily uniquely determined by these criteria.")
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

# ------------------------------------------------------------------------------
#> These aliases are reference-like in that both _x_ and _someValue_ refer to the same underlying data
#> and modifications to either are visible to both.
#> Algorithm steps that want to avoid this reference-like behaviour
#> should explicitly make a copy of the right-hand side:
#> “Let _x_ be a copy of _someValue_” creates a shallow copy of _someValue_.

@P("{EXPR} : a copy of {EX}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        (t, env1) = tc_expr(var, env0); assert env1 is env0
        return (t, env1)

    def d_exec(expr):
        [var] = expr.children
        # It could, of course, be something other than a List,
        # but in practice, Lists are the only things we copy?
        L = EXEC(var, ES_List)
        return L.copy()

# ------------------------------------------------------------------------------
#> Once declared, an alias may be referenced in any subsequent steps
#> and must not be referenced from steps prior to the alias's declaration.

@P("{SETTABLE} : {var}")
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

    d_exec = d_exec_pass_down

# ------------------------------------------------------------------------------
# (declaring an alias for the scope of a single expression)

@P("{EXPR} : {EX}, where {DEFVAR} is {EX}")
class _:
    def s_expr(expr, env0, _):
        [exa, var, exb] = expr.children
        (exb_type, env1) = tc_expr(exb, env0); assert env1 is env0
        env2 = env1.plus_new_entry(var, exb_type)
        (exa_type, env3) = tc_expr(exa, env2)
        return (exa_type, env3)

    def d_exec(expr):
        [exa, var, exb] = expr.children
        value = EXEC(exb, E_Value)
        curr_frame().start_contour()
        curr_frame().let_var_be_value(var, value)
        result = EXEC(exa, E_Value)
        curr_frame().end_contour()
        return result

@P("{EXPR} : {EX}, where {DEFVAR} is {EX} and {DEFVAR} is {EX}")
@P("{EXPR} : {EX}, where {DEFVAR} is {EX}, and {DEFVAR} is {EX}")
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
#> Aliases may be modified using the form “Set _x_ to _someOtherValue_”.

@P("{COMMAND} : Set {SETTABLE} to {EXPR}.")
@P("{COMMAND} : Set {SETTABLE} to {MULTILINE_EXPR}")
@P("{SMALL_COMMAND} : set {SETTABLE} to {EXPR}")
class _:
    def s_nv(anode, env0):
        [settable, expr] = anode.children
        return env0.set_A_to_B(settable, expr)

    def d_exec(command):
        [settable, expr] = command.children
        value = EXEC(expr, E_Value)
        curr_frame().set_settable_to_value(settable, value)

# ------------------------------------------------------------------------------
# (This section is where "Return" steps should be mentioned?)

@P("{COMMAND} : Return {EXPR}.")
@P("{COMMAND} : Return {EXPR}. This may be of type Reference.")
@P("{COMMAND} : Return {MULTILINE_EXPR}")
@P("{SMALL_COMMAND} : return {EXPR}")
class _:
    def s_nv(anode, env0):
        [expr] = anode.children
        (t1, env1) = tc_expr(expr, env0)
        # assert env1 is env0
        if False and trace_this_op:
            print("Return command's expr has type", t1)
        proc_add_return(env1, t1, anode)
        return None

    def d_exec(command):
        [expr] = command.children
        curr_frame().start_returning(EXEC(expr, E_Value))

# ------------------------------------------------------------------------------
# (This section is where "Note" steps should be mentioned?)

@P("{COMMAND} : {note}")
class _:
    def s_nv(anode, env0):
        return env0

# ------------------------------------------------------------------------------
# (This section is where conditions should be mentioned?)

@P("{CONDITION} : {CONDITION_1}")
@P("{CONDITION_1} : {TYPE_TEST}")
@P("{CONDITION_1} : {NUM_COMPARISON}")
@P("{CONDITION_1} : {NUM_COMPARISON} (ignoring potential non-monotonicity of time values)")
class _:
    def s_cond(cond, env0, asserting):
        [child] = cond.children
        return tc_cond(child, env0, asserting)

    def d_exec(cond):
        [child] = cond.children
        return EXEC(child, bool)

@P("{CONDITION} : {CONDITION_1} or {CONDITION_1}")
@P("{CONDITION} : {CONDITION_1}, or if {CONDITION_1}")
@P("{CONDITION} : {CONDITION_1}, {CONDITION_1}, or {CONDITION_1}")
@P("{CONDITION} : {CONDITION_1}, {CONDITION_1}, {CONDITION_1}, or {CONDITION_1}")
class _:
    def s_cond(cond, env0, asserting):
        logical = ('or', cond.children)
        return tc_logical(logical, env0, asserting)

    def d_exec(condition):
        return any(
            EXEC(cond, bool)
            for cond in condition.children
        )

@P("{CONDITION} : {CONDITION_1} and {CONDITION_1}")
@P("{CONDITION} : {CONDITION_1}, {CONDITION_1}, and {CONDITION_1}")
@P("{CONDITION} : {CONDITION_1}, {CONDITION_1}, {CONDITION_1}, and {CONDITION_1}")
class _:
    def s_cond(cond, env0, asserting):
        logical = ('and', cond.children)
        return tc_logical(logical, env0, asserting)

    def d_exec(cond):
        return all(
            EXEC(subcond, bool)
            for subcond in cond.children
        )

@P("{CONDITION} : {CONDITION_1}, or if {CONDITION_1} and {CONDITION_1}")
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

@P("{CONDITION} : {CONDITION_1} or {CONDITION_1} <ins>and {CONDITION_1}</ins>")
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

@P("{CONDITION} : {CONDITION_1} and {CONDITION_1}, or if {CONDITION_1} and {CONDITION_1}")
@P("{CONDITION} : {CONDITION_1} and {CONDITION_1}, or {CONDITION_1} and {CONDITION_1}")
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

@P("{CONDITION} : ({NUM_COMPARISON} or {NUM_COMPARISON}) and ({NUM_COMPARISON} or {NUM_COMPARISON})")
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

@P("{CONDITION} : {CONDITION_1} unless {CONDITION_1}")
@P("{CONDITION} : {CONDITION_1}, unless {CONDITION_1}")
class _:
    def s_cond(cond, env0, asserting):
        [conda, condb] = cond.children
        tc_cond(conda, env0)
        tc_cond(condb, env0)
        return (env0, env0)

    def d_exec(cond):
        [conda, condb] = cond.children
        return EXEC(conda, bool) and not EXEC(condb, bool)

@P("{CONDITION} : {CONDITION_1} unless {CONDITION_1} and {CONDITION_1}")
class _:
    def s_cond(cond, env0, asserting):
        [conda, condb, condc] = cond.children
        tc_cond(conda, env0)
        tc_cond(condb, env0)
        tc_cond(condc, env0)
        return (env0, env0)

# ==============================================================================
#@ 5.2.1 Abstract Operations

@P("{COMMAND} : Perform {PP_NAMED_OPERATION_INVOCATION}.")
@P("{COMMAND} : Perform {PP_NAMED_OPERATION_INVOCATION}. {note}")
@P("{SMALL_COMMAND} : perform {PP_NAMED_OPERATION_INVOCATION}")
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

@P("{PP_NAMED_OPERATION_INVOCATION} : {NAMED_OPERATION_INVOCATION}")
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

    d_exec = d_exec_pass_down

@P("{NAMED_OPERATION_INVOCATION} : {h_emu_meta_start}{NAMED_OPERATION_INVOCATION}{h_emu_meta_end}")
class _:
    def s_expr(expr, env0, _):
        [_, noi, _] = expr.children
        return tc_expr(noi, env0)

@P("{NAMED_OPERATION_INVOCATION} : {PREFIX_PAREN} (see {h_emu_xref})")
class _:
    def s_expr(expr, env0, _):
        [pp, _] = expr.children
        return tc_expr(pp, env0)

# ------------------------------------------------------------------------------
#> Abstract operations are typically referenced using a functional application style
#> such as OperationName(_arg1_, _arg2_).

@P("{PREFIX_PAREN} : {OPN_BEFORE_PAREN}({EXLIST_OPT})")
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

            (_, env2) = tc_args(params, args, env0, expr)
            return (return_type, env2)

        elif opn_before_paren.prod.rhs_s == r'{var}.{cap_word}':
            [var, cap_word] = opn_before_paren.children
            return tc_invocation_of_record_method(var, cap_word, args, expr, env0)

        elif opn_before_paren.prod.rhs_s == '{SIMPLE_OPERATION_NAME}':
            callee_op_name = opn_before_paren.source_text()
            callee_op = spec.alg_info_['op'][callee_op_name]
            if callee_op.species == 'op: discriminated by syntax: steps':
                add_pass_error(
                    expr,
                    "Unusual to invoke a SDO via prefix-paren notation: " + expr.source_text()
                )
                assert len(args) == 1
                return tc_sdo_invocation(callee_op_name, args[0], [], expr, env0)

            assert callee_op.species.startswith('op: singular'), callee_op.species

            if callee_op.headers == []:
                # The spec (probably) defines this operation,
                # but in way that isn't amenable to processing.
                # In particular, we don't have a structured header
                # that would give the parameter-type(s) and return-type.
                # So we basically have to hard-code the analysis for each operation.
                return tc_invocation_of_ad_hoc_op(callee_op_name, args, env0)

            return tc_invocation_of_singular_op(callee_op, args, expr, env0)

        else:
            assert 0, opn_before_paren.prod.rhs_s

    def d_exec(expr):
        [opn_before_paren, exlist_opt] = expr.children
        opr = opn_before_paren.prod.rhs_s
        if opr == '{SIMPLE_OPERATION_NAME}':
            op_name = opn_before_paren.source_text()
        else:
            assert NYI
        #
        arg_values = EXEC(exlist_opt, list)
        return apply_op_to_arg_values(op_name, arg_values)

@P("{NAMED_OPERATION_INVOCATION} : the result of performing {cap_word} on {EX}")
# This has the syntax of an SDO invocation, but it actually invokes an AO.
class _:
    def s_expr(expr, env0, _):
        [callee, local_ref] = expr.children[0:2]
        callee_op_name = callee.source_text()
        assert callee_op_name == 'UTF16EncodeCodePoint'
        callee_op = spec.alg_info_['op'][callee_op_name]
        return tc_invocation_of_singular_op(callee_op, [local_ref], expr, env0)

    def d_exec(expr):
        [cap_word, arg] = expr.children
        [op_name] = cap_word.children
        arg_value = EXEC(arg, E_Value)
        return apply_op_to_arg_values(op_name, [arg_value])

# ----------------------------------------------------------

@P("{EXLIST_OPT} : {EXLIST}")
class _:
    def d_exec(exlist_opt):
        [exlist] = exlist_opt.children
        return EXEC(exlist, list)

@P("{EXLIST} : {EXLIST}, {EX}")
class _:
    def d_exec(anode):
        [exlist, ex] = anode.children
        return EXEC(exlist, list) + [EXEC(ex, E_Value)]

@P("{EXLIST} : {EX}")
class _:
    def d_exec(exlist):
        [ex] = exlist.children
        return [ EXEC(ex, E_Value) ]

# ----------------------------------------------------------

def apply_op_to_arg_values(op_name, arg_values):
    if isinstance(op_name, str):

        alg_info = spec.alg_info_['op'][op_name]
        assert alg_info.species in ['op: singular', 'op: singular: numeric method']

        alg_defns = alg_info.all_definitions()
        if len(alg_defns) == 0:
            # Pseudocode.py has calls like:
            # ensure_alg('op: singular', 'floor')
            # but no definition(s), so we arrive here.
            func = predefined_operations[op_name]
            return func(*arg_values)

        elif len(alg_defns) == 1:
            [alg_defn] = alg_defns
            return execute_alg_defn(alg_defn, arg_vals=arg_values)

        else:
            # Operation has multiple definitions, discriminated on the argument type.
            # (Should this be a different alg_info.species?)
            assert len(arg_values) == 1
            [arg_value] = arg_values

            matching_defns = [
                alg_defn
                for alg_defn in alg_defns
                if value_matches_discriminator(arg_value, alg_defn.discriminator)
            ]
            assert len(matching_defns) == 1
            [relevant_alg_defn] = matching_defns

            return execute_alg_defn(relevant_alg_defn, arg_vals=arg_values)

    else:
        assert NYI, op_name

def value_matches_discriminator(value, discriminator):
    assert value.isan(E_Value)
    assert isinstance(discriminator, str)
    value_type_name = type(value).__name__
    assert value_type_name.startswith('EL_')
    return (value_type_name == 'EL_' + discriminator)

# --------------------------------------

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

@P("{PROD_REF} : this phrase")
@P("{PROD_REF} : this production")
class _:
    def s_expr(expr, env0, _):
        assert env0.assoc_productions
        return (T_Parse_Node, env0)

    def d_exec(prod_ref):
        [] = prod_ref.children
        return curr_frame()._focus_node

@P("{PROD_REF} : this {nonterminal}")
class _:
    def s_expr(expr, env0, _):
        [nonterminal] = expr.children
        return_t = s_resolve_focus_reference('this', nonterminal, expr, env0)
        return (return_t, env0)

    def d_exec(expr):
        [nont] = expr.children
        fn = curr_frame()._focus_node
        assert fn.symbol == nt_name_from_nonterminal_node(nont)
        return fn

@P("{PROD_REF} : {nonterminal}")
class _:
    def s_expr(expr, env0, _):
        [nonterminal] = expr.children

        if env0.assoc_productions is None:
            # Since there are no associated productions (no focus node),
            # this is probably a reference to the *symbol*, not a Parse Node.
            # (This is almost always the second argument to ParseText.)
            return (T_grammar_symbol_, env0)

        return_t = s_resolve_focus_reference('', nonterminal, expr, env0)
        return (return_t, env0)

    def d_exec(prod_ref):
        [nont] = prod_ref.children
        if curr_frame().has_a_focus_node():
            nt_name = nt_name_from_nonterminal_node(nont)
            pnode = curr_frame().resolve_focus_reference(None, nt_name)
            return pnode
        else:
            # This isn't really a {PROD_REF}, it's a {G_SYM},
            # but we can't make the metagrammar ambiguous.
            return EXEC(nont, ES_NonterminalSymbol)

@P("{PROD_REF} : the {nonterminal}")
class _:
    def s_expr(expr, env0, _):
        nonterminal = expr.children[-1]
        return_t = s_resolve_focus_reference('the', nonterminal, expr, env0)
        return (return_t, env0)

    def d_exec(prod_ref):
        [nont] = prod_ref.children
        nt_name = nt_name_from_nonterminal_node(nont)
        return curr_frame().resolve_focus_reference(None, nt_name)

@P("{PROD_REF} : the derived {nonterminal}")
class _:
    def s_expr(expr, env0, _):
        [nont] = expr.children
        return_t = s_resolve_focus_reference('the derived', nont, expr, env0)
        return (return_t, env0)

    def d_exec(prod_ref):
        [nont] = prod_ref.children
        nt_name = nt_name_from_nonterminal_node(nont)
        return curr_frame().resolve_focus_reference('derived', nt_name)

@P("{PROD_REF} : the {ORDINAL} {nonterminal}")
class _:
    def s_expr(expr, env0, _):
        [ordinal, nonterminal] = expr.children
        ordinal_str = ordinal.source_text()
        ordinal_num = {
            'first' : 1,
            'second': 2,
            'third' : 3,
            'fourth': 4,
        }[ordinal_str]

        return_t = s_resolve_focus_reference(ordinal_num, nonterminal, expr, env0)
        return (return_t, env0)

    def d_exec(prod_ref):
        [ordinal, nont] = prod_ref.children
        ordinal_str = ordinal.source_text()
        ordinal_num = {
            'first' : 1,
            'second': 2,
            'third' : 3,
            'fourth': 4,
        }[ordinal_str]
        nt_name = nt_name_from_nonterminal_node(nont)
        return curr_frame().resolve_focus_reference(ordinal_num, nt_name)

@P('{PROD_REF} : the enclosing {nonterminal}')
class _:
    def s_expr(expr, env0, _):
        [nonterminal] = expr.children
        # We could look at env.assoc_productions
        # and check that there must be an enclosing {nonterminal},
        # but that's probably more bother than it's worth.
        return (ptn_type_for(nonterminal), env0)

def s_resolve_focus_reference(prefix, nonterminal, expr, env0):
    nt_name = nt_name_from_nonterminal_node(nonterminal)

    # Count the total number of RHSs
    total_n_rhss = 0
    for production in env0.assoc_productions:
        total_n_rhss += len(production._rhss)

    extra_t = T_0
    for (p_i, production) in enumerate(env0.assoc_productions, start=1):
        # We go to each production,
        # and count the number of occurrences of {nt_name}
        # on the LHS and RHS.
        lhs_count = (production._lhs_symbol == nt_name)
        for (r_i, rhs) in enumerate(production._rhss, start=1):
            named_r_items = [
                r_item
                for r_item in rhs._rhs_items
                if r_item.kind == 'GNT' and r_item._nt_name == nt_name
            ]
            rhs_count = len(named_r_items)
            r_items_to_check_for_optionality = []

            if total_n_rhss == 1:
                locator = 'the associated production'
            else:
                locator = f"production #{p_i}'s rhs #{r_i}"

            # TODO: Convert the following asserts into check-and-complain.

            if prefix == 'this':
                # {PROD_REF} : this {nonterminal}
                #
                # {nonterminal} must be the LHS of every associated production.
                # Doesn't matter how many occurrences on the RHS.
                assert lhs_count == 1

            elif prefix in ['', 'the']:
                # {PROD_REF} : {nonterminal}
                # {PROD_REF} : the {nonterminal}
                #
                # Each associated production
                # should have exactly 1 occurrence of {nt_name}
                # (including both LHS and RHS).
                total_count = lhs_count + rhs_count
                if total_count == 0:
                    # This seems like it should be an error, but there are 4 cases of
                    #    `If |BindingIdentifier| is present ...`
                    # where, in the associated productions, some have a BindingIdentifier and some don't.
                    # TODO: Check that some productions have {nt_name} and some don't.
                    # TODO: Only allow this within an 'is [not] present' test.
                    extra_t = T_not_in_node
                elif total_count != 1:
                    add_pass_error(
                        expr,
                        f"node-ref is ambiguous because {locator} has {total_count} occurrences of {nt_name}"
                    )
                r_items_to_check_for_optionality = named_r_items

            elif prefix == 'the derived':
                # {PROD_REF} : the derived {nonterminal}
                #
                # Each associated production
                # should have exactly 1 RHS occurrence of {nt_name}.
                # Moreover, it should also have {nt_name} as the LHS,
                # otherwise there's no reason to specify 'derived'.

                assert lhs_count == 1
                assert rhs_count == 1
                r_items_to_check_for_optionality = named_r_items

            elif isinstance(prefix, int):
                # {PROD_REF} : the {ORDINAL} {nonterminal}
                #
                N = prefix
                # Each associated production
                # should have at least {N} RHS occurrences of {nt_name},
                # and zero LHS occurrences
                # (otherwise it's ambiguous whether to start counting at the LHS).

                assert lhs_count == 0
                assert rhs_count >= N
                r_items_to_check_for_optionality = [ named_r_items[N-1] ]

            else:
                assert 0, prefix

            for r_item in r_items_to_check_for_optionality:
                if r_item._is_optional:
                    extra_t = T_not_in_node

    return ptn_type_for(nonterminal) | extra_t

# --------------
# "present"

# "X is [not] present" has 2 meanings:
# 1) X is a nonterminal that is optional in a relevant production,
#    and the corresponding child is [not] present in the relevant Parse Node.
#    (5.1.5.3 Optional Symbols)
# 2) X is an optional parameter (of an operation or a function),
#    and an arg value was [not] supplied for the current invocation.
#    (5.3 Algorithm Conventions)
#    TODO: get rid of this usage. (roll eyes at PR #953)
# (So there's a potential ambiguity if you pass a Parse Node to an optional parameter,
# but I don't think that ever happens.

@P("{CONDITION_1} : {LOCAL_REF} is present")
@P("{CONDITION_1} : {LOCAL_REF} is not present")
class _:
    def s_cond(cond, env0, asserting):
        [ex] = cond.children
        if ex.is_a('{PROD_REF}'):
            t = T_not_in_node
            # TODO: change the associated_productions in the resulting envs?
        elif ex.is_a('{var}'):
            # It should be the name of a parameter
            assert ex.source_text() in env0.parret.parameter_names
            if env0.alg_species.startswith('op:'):
                t = T_not_passed
            elif env0.alg_species.startswith('bif:'):
                # In a built-in function,
                # we can ask if *any* of the parameters is present,
                # regardless of whether they're marked optional or not.
                # So this form puts no pre-condition on the parameter's stype.
                # As for post-condition, in the resulting env where the parameter is not present,
                # we could restrict the parameter's stype to T_not_passed,
                # but it's probably not worth it.
                # E.g., a typical use is:
                #     If _param_ is not present, set _param_ to <default>.
                return (env0, env0)
            else:
                assert 0
        else:
            assert 0, ex.source_text()
        copula = 'is a' if 'not present' in cond.prod.rhs_s else 'isnt a'
        return env0.with_type_test(ex, copula, t, asserting)

    def d_exec(cond):
        [prod_ref] = cond.children
        pnode = EXEC(prod_ref, 'ParseNodeOrAbsent')
        if 'not present' in cond.prod.rhs_s:
            return pnode.isan(ES_AbsentParseNode)
        else:
            return pnode.isan(ES_ParseNode)

# ------------------------------------------------------------------------------
#> Syntax-directed operations are invoked with a parse node and, optionally, other parameters ...

@P("{NAMED_OPERATION_INVOCATION} : the {cap_word} of {LOCAL_REF}")
@P("{NAMED_OPERATION_INVOCATION} : the {cap_word} of {LOCAL_REF} (see {h_emu_xref})")
@P("{NAMED_OPERATION_INVOCATION} : the {cap_word} of {LOCAL_REF} as defined in {h_emu_xref}")
@P("{NAMED_OPERATION_INVOCATION} : {cap_word} of {LOCAL_REF}")
class _:
    def s_expr(expr, env0, _):
        [callee, local_ref] = expr.children[0:2]
        callee_op_name = callee.source_text()
        return tc_sdo_invocation(callee_op_name, local_ref, [], expr, env0)

    def d_exec(expr):
        [cap_word, local_ref] = expr.children
        return execute_sdo_invocation(cap_word, local_ref, [])

@P("{NAMED_OPERATION_INVOCATION} : the {cap_word} of {LOCAL_REF} {WITH_ARGS}")
@P("{NAMED_OPERATION_INVOCATION} : {cap_word} of {LOCAL_REF} {WITH_ARGS}")
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

    def d_exec(expr):
        [cap_word, local_ref, with_args] = expr.children
        return execute_sdo_invocation(cap_word, local_ref, flatten_with_args(with_args))

def flatten_with_args(with_args):
    p = str(with_args.prod)
    if p in [
        '{WITH_ARGS} : with argument {EX}',
        '{WITH_ARGS} : {PASSING} argument {EX}',
    ]:
        return with_args.children[-1:]
    elif p in [
        '{WITH_ARGS} : with arguments {EX} and {EX}',
        '{WITH_ARGS} : {PASSING} arguments {EX} and {EX}',
    ]:
        return with_args.children[-2:]
    else:
        assert NYI, p

# ------------------------------------------------------------------------------

def execute_sdo_invocation(sdo_name_arg, focus_expr, arg_exprs):
    if isinstance(focus_expr, ES_ParseNode):
        focus_node = focus_expr
    else:
        focus_node = EXEC(focus_expr, ES_ParseNode)

    arg_vals = [
        EXEC(arg_expr, E_Value)
        for arg_expr in arg_exprs
    ]

    if isinstance(sdo_name_arg, str):
        sdo_name = sdo_name_arg
    elif isinstance(sdo_name_arg, ANode):
        sdo_name = sdo_name_arg.source_text()
    else:
        assert 0

    trace_this = False
    if trace_this:
        stderr('-' * 40)
        stderr(f"Applying {sdo_name} to a {focus_node.puk}")

    sdo_map = spec.sdo_coverage_map[sdo_name]

    if sdo_name == 'Early Errors':
        assert 0 # handled elsewhere

    elif sdo_name in ['Contains', 'AllPrivateIdentifiersValid', 'ContainsArguments']:
        if trace_this:
            stderr(f"{sdo_name} is a default-and-explicits style of SDO,")
            stderr(f"    so check for an explicit definition that is associated with that production.")
        if focus_node.puk in sdo_map:
            if trace_this: stderr("There is one, so we use it.")
            puk = focus_node.puk
        else:
            if trace_this: stderr("There isn't one, so we use the default definition.")
            puk = ('*default*', '', '')

    else:
        # The chain rule applies
        if trace_this:
            stderr(f"{sdo_name} is an explicits-plus-chaining style of SDO.")
            stderr(f"Looking for a defn...")

        while True:
            if trace_this: stderr(f"    key {focus_node.puk}")
            if focus_node.puk in sdo_map:
                if trace_this: stderr(f"    has a defn!")
                puk = focus_node.puk
                break
            if trace_this: stderr(f"    no defn")
            if focus_node.is_instance_of_chain_prod:
                if trace_this: stderr(f"    but we can chain to {focus_node.direct_chain}")
                focus_node = focus_node.direct_chain
            else:
                if trace_this: stderr(f"    and the chain rule doesn't apply, so ERROR")
                stderr(f"SPEC BUG: {sdo_name} not defined on {focus_node.puk}")
                stderr(f"  for {focus_node.text()}")

                if sdo_name == 'PropName' and focus_node.puk == ('CoverInitializedName', 'IdentifierReference Initializer', ''):
                    # This isn't a spec bug per se, but the spec expresses itself
                    # in a way that's hard for me to mechanize.
                    # (Other rules should prevent us getting here.)
                    return EL_String([])

                if sdo_name == 'SV':
                    return EL_String([])

                if sdo_name == 'VarDeclaredNames':
                    return ES_List([])

                if sdo_name.startswith('Contains'):
                    return EL_Boolean(False)

                # return ES_List([])
                assert 0

    sdo_defns = sdo_map[puk]
    assert len(sdo_defns) == 1
    [sdo_defn] = sdo_defns

    return execute_alg_defn(sdo_defn, focus_node=focus_node, arg_vals=arg_vals)

# ==============================================================================
#@ 5.2.3 Runtime Semantics

# ==============================================================================
#@ 5.2.3.2 Throw an Exception

#> Algorithms steps that say to throw an exception, such as
#>   1. Throw a *TypeError* exception.
#> mean the same things as:
#>   1. Return ThrowCompletion(a newly created *TypeError* object).

@P("{COMMAND} : Throw a {ERROR_TYPE} exception.")
@P("{SMALL_COMMAND} : throw a {ERROR_TYPE} exception because the structure is cyclical")
@P("{SMALL_COMMAND} : throw a {ERROR_TYPE} exception")
class _:
    def s_nv(anode, env0):
        [error_type] = anode.children
        proc_add_return(env0, ThrowCompletionType(type_for_ERROR_TYPE(error_type)), anode)
        return None

# ==============================================================================
#@ 5.2.3.3 ReturnIfAbrupt

#> Algorithms steps that say or are otherwise equivalent to:
#>     1. ReturnIfAbrupt(_argument_).
#> mean the same thing as:
#>     1. If _argument_ is an abrupt completion, return _argument_.
#>     1. Else if _argument_ is a Completion Record, set _argument_ to _argument_.[[Value]].
#>
#> Algorithms steps that say or are otherwise equivalent to:
#>     1. ReturnIfAbrupt(AbstractOperation()).
#> mean the same thing as:
#>     1. Let _hygienicTemp_ be AbstractOperation().
#>     1. If _hygienicTemp_ is an abrupt completion, return _hygienicTemp_.
#>     1. Else if _hygienicTemp_ is a Completion Record, set _hygienicTemp_ to _hygienicTemp_.[[Value]].
#> Where _hygienicTemp_ is ephemeral and visible only in the steps pertaining to ReturnIfAbrupt.

@P("{COMMAND} : ReturnIfAbrupt({EX}).")
class _:
    def s_nv(anode, env0):
        [ex] = anode.children
        (_, env1) = handle_completion_record_shorthand('ReturnIfAbrupt', ex, env0)
        return env1

# ==============================================================================
#@ 5.2.3.4 ReturnIfAbrupt Shorthands

#> Invocations of abstract operations and syntax-directed operations
#> that are prefixed by ? indicate that ReturnIfAbrupt should be applied
#> to the resulting Completion Record.
#> For example, the step:
#>    1. ? OperationName().
#> is equivalent to the following step:
#>    1. ReturnIfAbrupt(OperationName())

@P("{PP_NAMED_OPERATION_INVOCATION} : ? {NAMED_OPERATION_INVOCATION}")
@P("{EX} : ? {DOTTING}")
@P("{EX} : ? {var}")
class _:
    def s_expr(expr, env0, _):
        [operand] = expr.children
        return handle_completion_record_shorthand('?', operand, env0)

# ------------------------------------------------------------------------------
#> Similarly, prefix ! is used to indicate that
#> the following invocation of an abstract or syntax-directed operation
#> will never return an abrupt completion
#> and that the resulting Completion Record's [[Value]] field
#> should be used in place of the return value of the operation.

@P("{PP_NAMED_OPERATION_INVOCATION} : ! {NAMED_OPERATION_INVOCATION}")
@P('{EX} : ! {var}')
class _:
    def s_expr(expr, env0, _):
        [noi] = expr.children
        return handle_completion_record_shorthand('!', noi, env0)

    def d_exec(expr):
        [noi] = expr.children
        value = EXEC(noi, E_Value)
        if value.isan(ES_CompletionRecord):
            assert not value.is_abrupt()
            return value.get_value_of_field_named('[[Value]]')
        else:
            return value

# ------------------------------------------------------------------------------

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
                tb = tb_for_object_with_slot(slotname_arg)
                (env2, _) = env1.with_type_test(obj_arg, 'is a', tb, False)

            elif prefix in ['ValidateTypedArray', 'ValidateIntegerTypedArray', 'ValidateAtomicAccessOnIntegerTypedArray']:
                # In the not-returning-early env,
                # the first arg is guaranteed to be a TypedArray.
                obj_arg = exes_in_exlist_opt(exlist_opt)[0]
                env2 = env1.with_expr_type_narrowed(obj_arg, T_TypedArray_object_)

            elif prefix == 'GeneratorValidate':
                gen_arg = exes_in_exlist_opt(exlist_opt)[0]
                env2 = env1.with_expr_type_narrowed(gen_arg, T_Generator_object_)

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

@P("{EE_RULE} : It is a Syntax Error if {CONDITION}.")
@P("{EE_RULE} : It is an early Syntax Error if {CONDITION}.")
class _:
    def s_nv(anode, env0):
        [cond] = anode.children
        tc_cond(cond, env0, False)
        return None

    def d_exec(anode):
        [cond] = anode.children
        if EXEC(cond, bool):
            it_is_a_syntax_error(anode)

@P("{EE_RULE} : It is a Syntax Error if {CONDITION}. Additional early error rules for {G_SYM} within direct eval are defined in {h_emu_xref}.")
@P("{EE_RULE} : It is a Syntax Error if {CONDITION}. Additional early error rules for {G_SYM} in direct eval are defined in {h_emu_xref}.")
class _:
    def s_nv(anode, env0):
        [cond, g_sym, h_emu_xref] = anode.children
        tc_cond(cond, env0)
        return None

    def d_exec(anode):
        [cond, g_sym, h_emu_xref] = anode.children
        if EXEC(cond, bool):
            it_is_a_syntax_error(anode)

@P("{EE_RULE} : If {CONDITION}, it is a Syntax Error if {CONDITION}.")
class _:
    def s_nv(anode, env0):
        [conda, condb] = anode.children
        (tenv, fenv) = tc_cond(conda, env0, False)
        tc_cond(condb, tenv, False)
        return None

    def d_exec(rule):
        [cond1, cond2] = rule.children
        if EXEC(cond1, bool) and EXEC(cond2, bool):
            it_is_a_syntax_error(rule)

@P("{EE_RULE} : It is a Syntax Error if {CONDITION}. This rule is not applied if {CONDITION}.")
class _:
    def s_nv(anode, env0):
        [conda, condb] = anode.children
        (t_env, f_env) = tc_cond(condb, env0)
        tc_cond(conda, f_env)
        return None

    def d_exec(rule):
        [conda, condb] = rule.children
        if not EXEC(condb, bool) and EXEC(conda, bool):
            it_is_a_syntax_error(rule)

@P("{EE_RULE} : <p>It is a Syntax Error if {CONDITION_1} and the following algorithm returns {BOOL_LITERAL}:</p>{nlai}{h_emu_alg}")
class _:
    def s_nv(anode, env0):
        [cond, bool_lit, h_emu_alg] = anode.children
        tc_cond(cond, env0)
        # XXX should check h_emu_alg
        return None

    def d_exec(rule):
        [cond, bool_lit, h_emu_alg] = rule.children
        if EXEC(cond, bool):
            bool_val = EXEC(bool_lit, EL_Boolean)
            emu_alg_body = h_emu_alg._hnode._syntax_tree

            EXEC(emu_alg_body, None)
            assert curr_frame().is_returning()
            alg_result = curr_frame().return_value
            curr_frame().stop_returning()

            if same_value(alg_result, bool_val):
                it_is_a_syntax_error(rule)

@P("{EE_RULE} : <p>{_indent_}{nlai}It is a Syntax Error if {LOCAL_REF} is<br>{nlai}{h_emu_grammar}<br>{nlai}and {LOCAL_REF} ultimately derives a phrase that, if used in place of {LOCAL_REF}, would produce a Syntax Error according to these rules. This rule is recursively applied.{_outdent_}{nlai}</p>")
class _:
    def s_nv(anode, env0):
        [local_ref1, h_emu_grammar, local_ref2, local_ref3] = anode.children
        env0.assert_expr_is_of_type(local_ref1, T_Parse_Node)
        env1 = env0.copy()
        env1.assoc_productions = h_emu_grammar._hnode._gnode._productions
        env1.assert_expr_is_of_type(local_ref2, T_Parse_Node)
        env0.assert_expr_is_of_type(local_ref3, T_Parse_Node)
        return None

    def d_exec(rule):
        [local_ref1, h_emu_grammar, local_ref2, local_ref3] = rule.children
        assert len(h_emu_grammar._hnode.puk_set) == 1
        [puk] = list(h_emu_grammar._hnode.puk_set)
        pnode = EXEC(local_ref1, ES_ParseNode)
        inner_pnode = pnode_unit_derives_a_node_with_puk(pnode, puk)
        if inner_pnode is None: return # no Syntax Error
        # BUG:
        # phrase = resolve local_ref2 wrt inner_pnode
        # "ultimately" derives? 
        # "these rules"?

@P("{EE_RULE} : If {CONDITION}, the Early Error rules for {h_emu_grammar} are applied.")
class _:
    def s_nv(anode, env0):
        [cond, h_emu_grammar] = anode.children
        tc_cond(cond, env0, False)
        return None

    def d_exec(rule):
        [cond, emu_grammar] = rule.children
        # PR:
        # This is weird.
        # It's saying that I need to take the EE rules for production A
        # and apply them to a Parse Node that's an instance of a different production B.
        #
        # In general, this wouldn't even make sense,
        # because the EE rules for production A typically refer to symbols on the RHS of the production,
        # which generally wouldn't have any meaning for an instance of a production B.
        #
        # However, in the 4 occurrences of this rule, it does make sense:
        assert cond.source_text() == "the source text matched by |FormalParameters| is strict mode code"
        assert emu_grammar.source_text() == "<emu-grammar>UniqueFormalParameters : FormalParameters</emu-grammar>"
        # `UniqueFormalParameters : FormalParameters` only has 1 Early Error rule,
        # and it only refers to |FormalParameters|, which *does* have meaning for the focus node.

        if EXEC(cond, bool):
            ee_map = spec.sdo_coverage_map['Early Errors']
            puk = ('UniqueFormalParameters', 'FormalParameters', '')
            ee_rules = ee_map[puk]
            for ee_rule in ee_rules:
                execute_alg_defn(ee_rule, focus_node=curr_frame()._focus_node)

@P("{EE_RULE} : For each {nonterminal} {DEFVAR} in {NAMED_OPERATION_INVOCATION}: It is a Syntax Error if {CONDITION}.")
class _:
    def s_nv(anode, env0):
        [nont, var, noi, cond] = anode.children
        t = ptn_type_for(nont)
        env1 = env0.ensure_expr_is_of_type(noi, ListType(t))
        env2 = env1.plus_new_entry(var, t)
        tc_cond(cond, env2)
        return None

    def d_exec(rule):
        [nont, defvar, noi, cond] = rule.children
        nt_name = nt_name_from_nonterminal_node(nont)
        L = EXEC(noi, ES_List)
        for pnode in L.elements():
            assert pnode.symbol == nt_name

            curr_frame().start_contour()
            curr_frame().let_var_be_value(defvar, pnode)
            if EXEC(cond, bool):
                it_is_a_syntax_error(cond)
            curr_frame().end_contour()

# ------------------------------------------------------------------------------

def it_is_a_syntax_error(rule):
    if isinstance(rule, ANode): rule = rule.source_text()
    error = EarlyError('Syntax Error', curr_frame()._focus_node, rule)
    ds.agent.early_errors.append(error)
    if ds.verbosity >= 1: stderr(f"Found early error: {error}")

@dataclass(frozen=True)
class EarlyError:
    kind: str
    location: ES_ParseNode
    condition: ANode

# ==============================================================================
#@ 5.2.5 Mathematical Operations

#> This specification makes reference to these kinds of numeric values:
#>  -- <dfn>Mathematical values</dfn>: Arbitrary real numbers, used as the default numeric type.
#>  -- <dfn>Extended mathematical values</dfn>: Mathematical values together with +∞ and -∞.
#>  -- <em>Numbers</em>: IEEE 754-2019 double-precision floating point values.
#>  -- <em>BigInts</em>: ECMAScript language values representing arbitrary integers in a one-to-one correspondence.

@dataclass
class ES_Mathnum(ES_Value):
    val: typing.Union[float, int]

    @staticmethod
    def compare(a, rator, b):
        if isinstance(rator, ANode):
            rator_s = rator.source_text()
        elif isinstance(rator, str):
            rator_s = rator
        else:
            assert NYI

        if rator_s == '\u2264': # "≤" U+2264 Less-Than or Equal To
            return (a.val <= b.val)
        elif rator_s in ['\u2265', 'is greater than or equal to']: # "≥" U+2265 Greater-Than or Equal To
            return (a.val >= b.val)
        elif rator_s in ['&gt;', 'is strictly greater than']:
            return (a.val > b.val)
        else:
            assert NYI, rator_s

    def __add__(self, other): return ES_Mathnum(self.val + other.val)
    def __sub__(self, other): return ES_Mathnum(self.val - other.val)
    def __mul__(self, other): return ES_Mathnum(self.val * other.val)
    def __truediv__(self, other): return ES_Mathnum(self.val / other.val)

    def __mod__(self, other):
        assert isinstance(self.val, int)
        assert isinstance(other.val, int)
        assert other.val != 0
        return ES_Mathnum(self.val % other.val)

# ------------------------------------------------------------------------------
#> This specification makes reference to these kinds of numeric values:
#> - <dfn>Mathematical values</dfn>
#> - <dfn>Extended mathematical values</dfn>: Mathematical values together with +∞ and -∞.
#> - <em>Numbers</em>: IEEE 754-2019 double-precision floating point values.
#> - <em>BigInts</em>: ECMAScript language values representing arbitrary integers in a one-to-one correspondence.

@P("{VAL_DESC} : a mathematical value")
class _:
    s_tb = T_MathReal_

@P("{VAL_DESC} : a non-negative extended mathematical value")
class _:
    s_tb = a_subset_of(T_MathReal_ | T_MathPosInfinity_)

# ------------------------------------------------------------------------------
#> This specification denotes most numeric values in base 10;

@P("{MATH_LITERAL} : {dec_int_lit}")
class _:
    s_tb = a_subset_of(T_MathInteger_)

    def s_expr(expr, env0, _):
        [lit] = expr.children
        return (T_MathInteger_, env0)

    d_exec = d_exec_pass_down

@P(r"{dec_int_lit} : \b [0-9]+ (?![0-9A-Za-z])")
class _:
    def s_expr(expr, env0, _):
        return (T_MathNonNegativeInteger_, env0)

    def d_exec(lit):
        [chars] = lit.children
        return ES_Mathnum(int(chars, 10))

@P("{BASE} : 10")
@P("{BASE} : 2")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_MathInteger_, env0)

    def d_exec(expr):
        [] = expr.children
        return ES_Mathnum(int(expr.source_text()))

@P("{MATH_LITERAL} : 64 (that is, 8<sup>2</sup>)")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_MathInteger_, env0)

@P("{MATH_LITERAL} : 0.5")
@P("{MATH_LITERAL} : 3π")
@P("{MATH_LITERAL} : 8.64")
@P("{MATH_LITERAL} : π")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_MathReal_, env0)

# ------------------------------------------------------------------------------
#> it also uses numeric values of the form
#> 0x followed by digits 0-9 or A-F as base-16 values.

@P("{MATH_LITERAL} : {hex_int_lit}")
class _:
    def s_expr(expr, env0, _):
        [hex_int_lit] = expr.children
        return (T_MathInteger_, env0)

    d_exec = d_exec_pass_down

@P(r"{hex_int_lit} : \b 0x [0-9A-F]{2,6} \b")
class _:
    def d_exec(hex_int_lit):
        [chars] = hex_int_lit.children
        return ES_Mathnum(int(chars, 16))

# ------------------------------------------------------------------------------
#> In general, when this specification refers to a numerical value,
#> such as in the phrase, "the length of _y_"
#> or "the integer represented by the four hexadecimal digits ...",
#> without explicitly specifying a numeric kind,
#> the phrase refers to a mathematical value.

# ------------------------------------------------------------------------------
#> When the term <dfn>integer</dfn> is used in this specification,
#> it refers to a mathematical value which is in the set of integers,
#> unless otherwise stated.

@P("{VAL_DESC} : an integer")
class _:
    s_tb = T_MathInteger_

@P("{VAL_DESC} : a positive integer")
class _:
    s_tb = a_subset_of(T_MathNonNegativeInteger_)

@P("{VAL_DESC} : a non-negative integer")
class _:
    s_tb = T_MathNonNegativeInteger_ # currently mapped to MathInteger_

@P("{VAL_DESC} : a non-negative integer that is evenly divisible by 4")
class _:
    s_tb = a_subset_of(T_MathNonNegativeInteger_)

@P("{VAL_DESC} : an integer ≥ {dsb_word}")
class _:
    s_tb = a_subset_of(T_MathInteger_)

# ------------------------------------------------------------------------------
#> When the term <dfn>integral Number</dfn> is used in this specification,
#> it refers to a Number value whose mathematical value is in the set of integers.

@P("{VAL_DESC} : an integral Number")
class _:
    s_tb = T_IntegralNumber_

@P("{VAL_DESC} : an odd integral Number")
class _:
    s_tb = a_subset_of(T_IntegralNumber_)

@P("{VAL_DESC} : a non-negative integral Number")
class _:
    s_tb = a_subset_of(T_IntegralNumber_)

@P("{VAL_DESC} : a non-negative finite Number")
class _:
    s_tb = a_subset_of(T_FiniteNumber_)

# ------------------------------------------------------------------------------
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

@P("{SUM} : {TERM} {SUM_OPERATOR} {TERM}")
@P("{SUM} : {SUM} {SUM_OPERATOR} {TERM}")
@P("{PRODUCT} : {TERM} {PRODUCT_OPERATOR} {FACTOR}")
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

                (T_BigInt, '+'      , T_BigInt): T_BigInt,
                (T_BigInt, '-'      , T_BigInt): T_BigInt,
                (T_BigInt, '×'      , T_BigInt): T_BigInt,

                # --------

                # misc:

                (T_not_set     , '×'      , T_MathInteger_): 'A is non-numeric',
                (T_tilde_empty_, '-'      , T_MathInteger_): 'A is non-numeric',

                (T_MathInteger_        , '+', T_tilde_auto_     ): 'B is non-numeric',

            }[triple]

            if result_t == 'A is non-numeric':
                add_pass_error(a, f"ST of operand is {a_t}, which includes {a_mt}, which is non-numeric")
                result_t = T_MathInteger_ # XXX
            elif result_t == 'B is non-numeric':
                add_pass_error(b, f"ST of operand is {b_t}, which includes {b_mt}, which is non-numeric")
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

    def d_exec(anode):
        [randA, rator, randB] = anode.children
        op = rator.source_text()
        a = EXEC(randA, ES_Mathnum)
        b = EXEC(randB, ES_Mathnum)
        if op in ['+', 'plus']: return a + b
        elif op in ['&times;', 'times', '\xd7']: return a * b
        elif op == '-': return a - b
        elif op == '/': return a / b
        elif op == 'modulo':
            #> The notation "_x_ modulo _y_" (_y_ must be finite and non-zero)
            #> computes a value _k_ of the same sign as _y_ (or zero) such that
            #> abs(_k_) < abs(_y_) and _x_ - _k_ = _q_ * _y_ for some integer _q_.
            return a % b
        else:
            assert NYI, op

@P("{PRODUCT} : {UNARY_OPERATOR}{FACTOR}")
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

@P("{EXPR} : the negative of {EX}")
class _:
    def s_expr(expr, env0, _):
        [ex] = expr.children
        (ex_t, env1) = tc_expr(ex, env0); assert env1 is env0
        assert ex_t == T_TBD or ex_t == T_MathInteger_
        return (ex_t, env0)

@P("{EX} : the remainder of dividing {EX} by {EX}")
@P("{EX} : The remainder of dividing {EX} by {EX}")
class _:
    def s_expr(expr, env0, _):
        [aex, bex] = expr.children
        env0.assert_expr_is_of_type(aex, T_MathInteger_)
        env0.assert_expr_is_of_type(bex, T_MathInteger_)
        return (T_MathInteger_, env0)

@P("{FACTOR} : {BASE}<sup>{EX}</sup>")
@P("{NUM_EXPR} : {EX} raised to the power {EX}")
class _:
    def s_expr(expr, env0, _):
        [a, b] = expr.children
        (a_t, env1) = tc_expr(a, env0); assert env1 is env0
        if a_t.is_a_subtype_of_or_equal_to(T_MathInteger_):
            env0.assert_expr_is_of_type(b, T_MathInteger_)
            result_t = T_MathInteger_
        elif a_t.is_a_subtype_of_or_equal_to(T_BigInt):
            env0.assert_expr_is_of_type(b, T_BigInt)
            result_t = T_BigInt
        else:
            assert 0, a_t
        return (result_t, env0) # unless exponent is negative

    def d_exec(expr):
        [base_expr, exponent_expr] = expr.children
        base_val = EXEC(base_expr, ES_Mathnum)
        exponent_val = EXEC(exponent_expr, ES_Mathnum)
        return ES_Mathnum(base_val.val ** exponent_val.val)

@P("{EXPR} : the result of raising {EX} to the {EX} power")
class _:
    def s_expr(expr, env0, _):
        [avar, bvar] = expr.children
        env1 = env0.ensure_expr_is_of_type(avar, T_MathReal_)
        env2 = env0.ensure_expr_is_of_type(bvar, T_MathReal_)
        return (T_MathReal_, env2)

@P("{EXPR} : the result of the {MATH_FUNC} of {EX}")
class _:
    def s_expr(expr, env0, _):
        [math_func, ex] = expr.children
        env1 = env0.ensure_expr_is_of_type(ex, T_Number | T_MathReal_)
        return (T_MathReal_, env1)

@P('{EXPR} : the inverse tangent of {EX}')
class _:
    def s_expr(expr, env0, _):
        [ex] = expr.children
        env1 = env0.ensure_expr_is_of_type(ex, T_MathReal_)
        return (T_MathReal_, env1)

@P("{EXPR} : the result of subtracting 1 from the exponential function of {EX}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_MathReal_)
        return (T_MathReal_, env1)

@P("{EXPR} : the square root of the sum of squares of the mathematical values of the elements of {var}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_List)
        return (T_MathReal_, env0)

@P("{EXPR} : an implementation-defined choice of either {var} or {var}")
class _:
    def s_expr(expr, env0, _):
        [vara, varb] = expr.children
        env0.assert_expr_is_of_type(vara, T_MathReal_)
        env0.assert_expr_is_of_type(varb, T_MathReal_)
        return (T_MathReal_, env0)

# comparisons:

@P("{CONDITION_1} : {var} is even")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_MathInteger_)
        return (env0, env0)

@P("{NUM_COMPARISON} : {NUM_COMPARAND} {NUM_COMPARATOR} {NUM_COMPARAND}")
class _:
    def s_cond(cond, env0, asserting):
        [a, op, b] = cond.children
        (a_t, env1) = tc_expr(a, env0);
        (b_t, env2) = tc_expr(b, env1);
        op_st = op.source_text()

        assert a_t != T_0
        assert b_t != T_0

        if op_st in ['=', '≠']:
            check_comparison(cond, '=', a_t, b_t)

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
                    (T_MathInteger_      , '>'   , T_not_passed        ): 'E',
                    (T_MathInteger_      , '>'   , T_tilde_empty_      ): 'E',
                    (T_MathInteger_      , '≤'   , T_not_passed        ): 'E',
                    (T_MathInteger_      , '≤'   , T_tilde_empty_      ): 'E',
                    (T_MathInteger_      , '≥'   , T_tilde_detached_   ): 'E',
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
                    (T_MathInteger_     , '&lt;', T_MathReal_        ): 'TF',
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
                    (T_IntegralNumber_         , '&lt;', T_IntegralNumber_         ): 'TF',
                    (T_NonIntegralFiniteNumber_, '≥'   , T_NonIntegralFiniteNumber_): 'TF',
                    (T_NonIntegralFiniteNumber_, '>'   , T_IntegralNumber_         ): 'TF',
                    (T_NonIntegralFiniteNumber_, '&lt;', T_IntegralNumber_         ): 'TF',
                    (T_NonIntegralFiniteNumber_, '&lt;', T_NonIntegralFiniteNumber_): 'TF',

                    # -------
                    # BigInt:

                    (T_BigInt, '>'   , T_BigInt): 'TF',
                    (T_BigInt, '&lt;', T_BigInt): 'TF',
                    (T_BigInt, '='   , T_BigInt): 'TF',
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

                    (T_tilde_bigint_, '≠', T_tilde_number_): 'TE',
                    (T_tilde_number_, '≠', T_tilde_bigint_): 'TE',

                    (T_tilde_bigint_, '≠', T_tilde_bigint_): 'FE',
                    (T_tilde_number_, '≠', T_tilde_number_): 'FE',

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

    def d_exec(comparison):
        [randA, ratorAB, randB] = comparison.children
        a = EXEC(randA, ES_Mathnum)
        b = EXEC(randB, ES_Mathnum)
        return ES_Mathnum.compare(a, ratorAB, b)

@P("{NUM_COMPARISON} : {NUM_COMPARAND} {NUM_COMPARATOR} {NUM_COMPARAND} {NUM_COMPARATOR} {NUM_COMPARAND}")
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

    def d_exec(comparison):
        [randA, ratorAB, randB, ratorBC, randC] = comparison.children
        a = EXEC(randA, ES_Mathnum)
        b = EXEC(randB, ES_Mathnum)
        c = EXEC(randC, ES_Mathnum)
        return ES_Mathnum.compare(a, ratorAB, b) and ES_Mathnum.compare(b, ratorBC, c)

@P("{CONDITION_1} : {var} is as small as possible")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_MathInteger_)
        return (env0, env0)

# ------------------------------------------------------------------------------

@P("{MATH_LITERAL} : +&infin;")
@P("{MATH_LITERAL} : +∞")
class _:
    s_tb = T_MathPosInfinity_

    def s_expr(expr, env0, _):
        return (T_MathPosInfinity_, env0)

@P("{MATH_LITERAL} : -&infin;")
@P("{MATH_LITERAL} : -∞")
class _:
    s_tb = T_MathNegInfinity_

    def s_expr(expr, env0, _):
        return (T_MathNegInfinity_, env0)

# ------------------------------------------------------------------------------
#> Conversions between mathematical values and Numbers or BigInts
#> are always explicit in this document.

#> A conversion from a mathematical value or extended mathematical value _x_
#> to a Number is denoted as "the Number value for _x_" or {fancy_f}(_x_),
#> and is defined in <emu-xref href="#sec-ecmascript-language-types-number-type"></emu-xref>.

@predefined_operations.put('\U0001d53d')
def _(mathnum):
    return the_Number_value_for(mathnum)

#> A conversion from an integer _x_ to a BigInt
#>     is denoted as "the BigInt value for _x_" or {fancy_z}(_x_).

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

@P("{EXPR} : the extended mathematical value of {var}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_FiniteNumber_ | T_PosInfinityNumber_ | T_NegInfinityNumber_)
        return (T_ExtendedMathReal_, env0)

# ------------------------------------------------------------------------------
#> The mathematical function abs(_x_) ...
#> The mathematical function min(_x1_, _x2_, &hellip; , _xN_) ...
#> The mathematical function max(_x1_, _x2_, ..., _xN_) ...

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

@P("{EXPR} : the result of clamping {var} between 0 and {EX}")
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
#> The mathematical function floor(_x_) produces the largest integer
#> (closest to +&infin;) that is not larger than _x_.
@predefined_operations.put('floor')
def _(mathnum):
    assert mathnum.isan(ES_Mathnum)
    return ES_Mathnum(math.floor(mathnum.val))

# ------------------------------------------------------------------------------
#> The mathematical function truncate(_x_) ...

# ------------------------------------------------------------------------------
#> Mathematical functions min, max, abs, and floor
#> are not defined for Numbers and BigInts,
#> and any usage of those methods that have non-mathematical value arguments
#> would be an editorial error in this specification.

# ------------------------------------------------------------------------------

def tc_invocation_of_ad_hoc_op(callee_op_name, args, env0):
    # These cases should maybe be farmed out to a DecoratedFuncDict,
    # so that they can be slotted in at the exact right spot.
    # (Combine it with predefined_operations.)
    # However, most of them are numeric operations,
    # so this is close enough for now.

    if callee_op_name == '𝔽': # U+1d53d MATHEMATICAL DOUBLE-STRUCK CAPITAL F (fancy_f)
        # mathematical to Number
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

    elif callee_op_name == 'ℤ': # U+2124 DOUBLE-STRUCK CAPITAL Z (fancy_z)
        # mathematical to BigInt
        assert len(args) == 1
        [arg] = args
        env0.assert_expr_is_of_type(arg, T_MathInteger_)
        return (T_BigInt, env0)

    elif callee_op_name == 'ℝ': # U+211d DOUBLE-STRUCK CAPITAL R (fancy_r)
        # Number/BigInt to mathematical
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
            return (T_MathReal_, env0)

    # ----------------------------------------------------------------

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
                else:
                    assert 0, t
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

    elif callee_op_name in ['floor', 'truncate']:
        assert len(args) == 1
        [arg] = args
        env1 = env0.ensure_expr_is_of_type(arg, T_MathReal_)
        return (T_MathInteger_, env1)

    # ----------------------------------------------------------------

    # defined in 22.2.2.9.5 MaybeSimpleCaseFolding
    elif callee_op_name == 'scf':
        assert len(args) == 1
        [arg] = args
        env0.assert_expr_is_of_type(arg, T_code_point_)
        return (T_code_point_, env0)

    else:
        assert 0, callee_op_name

# ------------------------------------------------------------------------------
#> An <dfn>interval</dfn> from lower bound _a_ to upper bound _b_
#> is a possibly-infinite, possibly-empty set of numeric values of the same numeric type.
#> Each bound will be described as either inclusive or exclusive, but not both.

@P("{INTERVAL} : the inclusive interval from {EX} to {EX}")
@P("{INTERVAL} : the interval from {EX} (inclusive) to {EX} (exclusive)")
class _:
    def s_expr(expr, env0, _):
        [lo, hi] = expr.children
        env0.assert_expr_is_of_type(lo, T_MathInteger_)
        env0.assert_expr_is_of_type(hi, T_MathInteger_)
        return (T_MathInteger_, env0)
        # Should maybe be ListType(T_MathInteger_) or something similar

@P("{CONDITION_1} : {var} is in {INTERVAL}")
@P("{CONDITION_1} : {var} is not in {INTERVAL}")
class _:
    def s_cond(cond, env0, asserting):
        [var, interval] = cond.children
        env0.assert_expr_is_of_type(interval, T_MathInteger_)
        (var_t, env1) = tc_expr(var, env0);

        if var_t == T_MathInteger_:
            return (env1, env1)

        elif var_t == T_MathInteger_ | T_MathNegInfinity_ | T_MathPosInfinity_:
            # It's well-defined to ask if an Infinity is in an interval:
            # it never is, because an interval has finite bounds.
            # (This arises in MakeFullYear, ToIndex, etc.)
            #
            # For the cases where the value is in the interval,
            # we can exclude the possibility that it's an Infinity:
            in_var = env1.with_expr_type_narrowed(var, T_MathInteger_)
            # For the cases where the value is *not* in the interval,
            # its static type still includes the possibility of Infinities.
            notin_var = env1

            if 'is in' in cond.prod.rhs_s:
                return (in_var, notin_var)
            elif 'is not in' in cond.prod.rhs_s:
                return (notin_var, in_var)
            else:
                assert 0
        else:
            assert 0, var_t

@P("{CONDITION_1} : there exists an integer {DEFVAR} in {INTERVAL} such that {CONDITION_1}")
class _:
    def s_cond(cond, env0, asserting):
        [i_var, interval, stcond] = cond.children
        env0.assert_expr_is_of_type(interval, T_MathInteger_)
        env_for_cond = env0.plus_new_entry(i_var, T_MathInteger_)
        return tc_cond(stcond, env_for_cond)

@P("{CONDITION_1} : {SETTABLE} ≠ {SETTABLE} for some integer {DEFVAR} in {INTERVAL}")
class _:
    def s_cond(cond, env0, asserting):
        [seta, setb, let_var, interval] = cond.children
        env0.assert_expr_is_of_type(interval, T_MathInteger_)
        env_for_settables = env0.plus_new_entry(let_var, T_MathInteger_)
        env_for_settables.assert_expr_is_of_type(seta, T_MathInteger_)
        env_for_settables.assert_expr_is_of_type(setb, T_MathInteger_)
        return (env0, env0)

@P("{VAL_DESC} : an integer in {INTERVAL}")
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

@P("{EACH_THING} : integer {DEFVAR} in {INTERVAL}")
class _:
    def s_nv(each_thing, env0):
        [loop_var, interval] = each_thing.children
        env0.assert_expr_is_of_type(interval, T_MathInteger_)
        return env0.plus_new_entry(loop_var, T_MathInteger_)

@P("{EXPR} : a List of the integers in {INTERVAL}, in ascending order")
@P("{EXPR} : a List of the integers in {INTERVAL}, in descending order")
class _:
    def s_expr(expr, env0, _):
        [interval] = expr.children
        env0.assert_expr_is_of_type(interval, T_MathNonNegativeInteger_)
        return (ListType(T_MathNonNegativeInteger_), env0)

@P('{VAL_DESC} : an integral Number in {INTERVAL}')
class _:
    def s_tb(val_desc, env):
        [interval] = val_desc.children
        if env is None:
            assert interval.source_text() in [
                "the inclusive interval from *+0*<sub>𝔽</sub> to *6*<sub>𝔽</sub>",
                "the inclusive interval from *+0*<sub>𝔽</sub> to *11*<sub>𝔽</sub>",
                "the inclusive interval from *+0*<sub>𝔽</sub> to *23*<sub>𝔽</sub>",
                "the inclusive interval from *+0*<sub>𝔽</sub> to *59*<sub>𝔽</sub>",
                "the inclusive interval from *+0*<sub>𝔽</sub> to *365*<sub>𝔽</sub>",
                "the inclusive interval from *+0*<sub>𝔽</sub> to *999*<sub>𝔽</sub>",
                "the inclusive interval from *1*<sub>𝔽</sub> to *31*<sub>𝔽</sub>",
                "the interval from *+0*<sub>𝔽</sub> (inclusive) to msPerDay (exclusive)",
            ], interval.source_text()
        else:
            env.assert_expr_is_of_type(interval, T_IntegralNumber_)
        return a_subset_of(T_IntegralNumber_)

# ------------------------------------------------------------------------------
# (The spec should talk about bit strings somewhere.)

@P("{EXPR} : the number of leading 1 bits in {var}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_MathNonNegativeInteger_)
        return (T_MathNonNegativeInteger_, env0)

@P("{EX} : the integer represented by the 32-bit two's complement bit string {var}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_MathInteger_) # bit string
        return (T_MathInteger_, env0)

@P("{EXPR} : the byte elements of {var} concatenated and interpreted as a bit string encoding of an unsigned little-endian binary number")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_MathInteger_))
        return (T_MathInteger_, env1)

@P("{EXPR} : the byte elements of {var} concatenated and interpreted as a bit string encoding of a binary little-endian two's complement number of bit length {PRODUCT}")
class _:
    def s_expr(expr, env0, _):
        [var, product] = expr.children
        env1 = env0.ensure_expr_is_of_type(product, T_MathInteger_ | T_Number); assert env1 is env0
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_MathInteger_))
        return (T_MathInteger_, env1)

@P("{EXPR} : the byte elements of {var} concatenated and interpreted as a little-endian bit string encoding of an IEEE 754-2019 binary32 value")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_MathInteger_))
        return (T_IEEE_binary32_, env1)

@P("{EXPR} : the byte elements of {var} concatenated and interpreted as a little-endian bit string encoding of an IEEE 754-2019 binary64 value")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_MathInteger_))
        return (T_IEEE_binary64_, env1)

@P("{EXPR} : the result of applying the bitwise AND operation to {var} and {var}")
@P("{EXPR} : the result of applying the bitwise exclusive OR (XOR) operation to {var} and {var}")
@P("{EXPR} : the result of applying the bitwise inclusive OR operation to {var} and {var}")
class _:
    def s_expr(expr, env0, _):
        [x, y] = expr.children
        env0.assert_expr_is_of_type(x, T_MathInteger_) # "bit string"
        env0.assert_expr_is_of_type(y, T_MathInteger_) # "bit string"
        return (T_MathInteger_, env0) # "bit string"

@P("{EXPR} : the 32-bit two's complement bit string representing {EX}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_MathInteger_)
        return (T_MathInteger_, env0) # bit string

@P("{EXPR} : a List whose elements are the {var}-byte binary encoding of {var}. The bytes are ordered in little endian order")
@P("{EXPR} : a List whose elements are the {var}-byte binary two's complement encoding of {var}. The bytes are ordered in little endian order")
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

@P("{EXPR} : the String representation of {EX}, formatted as a decimal number")
@P("{EXPR} : the String representation of {EX}, formatted as a lowercase hexadecimal number")
@P("{EXPR} : the String representation of {EX}, formatted as an uppercase hexadecimal number")
class _:
    def s_expr(expr, env0, _):
        [ex] = expr.children
        env1 = env0.ensure_expr_is_of_type(ex, T_Number | T_MathInteger_)
        return (T_String, env1)

@P("{EX} : the digits of the decimal representation of {var} (in order, with no leading zeroes)")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_MathInteger_)
        return (ListType(T_code_unit_), env0)

@P("{CONDITION_1} : the decimal representation of {var} has 20 or fewer significant digits")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_MathReal_)
        return (env0, env0)

    def d_exec(cond):
        [var] = cond.children
        mathnum = EXEC(var, ES_Mathnum)
        return number_of_significant_digits_in_decimal_representation_of(mathnum) <= 20

def number_of_significant_digits_in_decimal_representation_of(mathnum: ES_Mathnum):
    s = str(mathnum.val).replace('.', '')
    assert s.isdigit()
    return len(s.strip('0'))

@P("{EXPR} : the mathematical value denoted by the result of replacing each significant digit in the decimal representation of {var} after the 20th with a 0 digit")
@P("{EXPR} : the mathematical value denoted by the result of replacing each significant digit in the decimal representation of {var} after the 20th with a 0 digit and then incrementing it at the 20th position (with carrying as necessary)")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_MathReal_)
        return (T_MathReal_, env0)

# ==============================================================================
#@ 5.2.6 Value Notation

#> Values which are internal to the specification
#> and not directly observable from ECMAScript code
#> are indicated with a ~sans-serif~ typeface.

@dataclass(frozen=True)
class ES_Adhoc(ES_Value):
    chars: str

@P("{tilded_word} : ~ [-a-z0-9+]+ ~")
class _:
    def d_exec(tilded_word):
        [chars] = tilded_word.children
        return ES_Adhoc(chars)

@P("{LITERAL} : {tilded_word}")
class _:
    def s_tb(literal, env):
        [tilded_word] = literal.children
        return type_for_tilded_word(tilded_word)

    def s_expr(expr, env0, _):
        [tilded_word] = expr.children
        return (type_for_tilded_word(tilded_word), env0)

    d_exec = d_exec_pass_down

def type_for_tilded_word(tilded_word):
    assert tilded_word.prod.lhs_s == '{tilded_word}'
    [chars] = tilded_word.children
    assert chars[0] == '~'
    assert chars[-1] == '~'
    uchars = chars[1:-1].replace('-', '_').replace('+', '_')
    return HierType(f"tilde_{uchars}_")

# ==============================================================================
#@ 5.2.7 Identity

def same_value(a, b):
    assert a.isan(E_Value)
    assert b.isan(E_Value)
    if type(a) == type(b):
        return a == b
    else:
        return False

#> From the perspective of this specification,
#> the word “is” is used to compare two values for equality,
#> as in “If _bool_ is *true*, then ...”

# (So I'm putting most the "X is Y" forms here.)

@P("{CONDITION_1} : {EX} is not {PREFIX_PAREN}")
@P("{CONDITION_1} : {EX} is not {SETTABLE}")
@P("{CONDITION_1} : {EX} is {PREFIX_PAREN}")
@P("{CONDITION_1} : {EX} is {SETTABLE}")
class _:
    def s_cond(cond, env0, asserting):
        [exa, exb] = cond.children
        (exa_type, env1) = tc_expr(exa, env0)
        (exb_type, env2) = tc_expr(exb, env1)
        check_comparison(cond, 'is', exa_type, exb_type)

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

def check_comparison(comparison, comparator, ta, tb):
    cc_command = comparison.closest_containing('{COMMAND}')
    is_within_Assert = cc_command is not None and cc_command.prod.rhs_s.startswith('Assert: ')
    pref_comparator = preferred_comparator(ta, tb, is_within_Assert)
    if comparator != pref_comparator:
        add_pass_error(
            comparison,
            f"Should use `{pref_comparator}` to compare {ta} and {tb}"
        )

def preferred_comparator(ta, tb, is_within_Assert):
    # Given the static types of two operands in a comparison,
    # return a string that indicates the preferred way to compare them.

    # From #2877:
    # - use =, ≠, <, ≤, >, and ≥ for mathematical value and bigint comparisons (except in asserts);
    #
    # - use `is`, `is not`, ... for number comparisons
    #
    # - use SameValue(..., ...) is *true* for equality comparison of
    #   symbols (except well-known) / objects / unknown ECMAScript language values
    #
    # - use `is` and `is not` for equality comparison of
    #   all other values, including
    #      booleans,
    #      strings,
    #      well-known symbols,
    #      null,
    #      undefined,
    #      enums,
    #      etc;
    #   avoid "is different from" or "is the same as"

    if ta == T_bound_function_exotic_object_ and tb == T_constructor_object_:
        # My static type system thinks that these two stypes are disjoint,
        # so a comparison would never succeed.
        # (Below, common_t would be T_0.)
        # However, [[Construct]] for a bound function exotic object has
        # `SameValue(_F_, _newTarget_)`
        return 'SameValue'

    (common_t, _) = ta.split_by(tb)

    if common_t == T_0:
        return "INCOMPARABLE"

    if common_t.is_a_subtype_of_or_equal_to(T_MathReal_ | T_ExtendedMathReal_) or common_t == T_BigInt:
        if is_within_Assert:
            return 'is'
        else:
            return '='

    if common_t == ListType(T_code_point_):
        # So that it isn't handled by the T_List case
        return 'is'

    if common_t.is_a_subtype_of_or_equal_to(T_List):
        return 'are the same List'

    if common_t.is_a_subtype_of_or_equal_to(T_Record):
        return 'are the same X Record'

    # SameValue only accepts ECMAScript language values,
    # so if either operand might not be an ECMAScript language value,
    # you can't use SameValue.
    (_, ta_spec) = ta.split_by(T_Tangible_)
    (_, tb_spec) = tb.split_by(T_Tangible_)
    if ta_spec != T_0 or tb_spec != T_0:
        return 'is'

    # So at this point, we're guaranteed that both operands are ES language values.

    assert common_t.is_a_subtype_of_or_equal_to(T_Tangible_)

    if common_t.is_a_subtype_of_or_equal_to(T_Object):
        return 'SameValue'
    if T_Object.is_a_subtype_of_or_equal_to(common_t):
        return 'SameValue'

    if T_Symbol.is_a_subtype_of_or_equal_to(common_t):
        return 'SameValue'
        # Should use `is` if the symbols are well-known,
        # but the type system can't tell,
        # and they probably aren't.

    if common_t.is_a_subtype_of_or_equal_to(T_Undefined | T_Null | T_Boolean | T_Number | T_String):
        return 'is'

    if common_t == T_BigInt | T_IntegralNumber_:
        return 'INCOMPARABLE'

    assert 0, common_t

# -------------------

@P("{CONDITION_1} : {EX} and {EX} are distinct values")
class _:
    def s_cond(cond, env0, asserting):
        [exa, exb] = cond.children
        (exa_type, env1) = tc_expr(exa, env0)
        (exb_type, env2) = tc_expr(exb, env1)
        return (env2, env2)

@P("{CONDITION_1} : {EX} and {EX} are both {LITERAL}")
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

@P("{CONDITION_1} : {EX} and {EX} are both {LITERAL} or both {LITERAL}")
class _:
    def s_cond(cond, env0, asserting):
        # occurs once, in SameValueNonNumber
        [exa, exb, litc, litd] = cond.children
        assert litc.source_text() == '*true*'
        assert litd.source_text() == '*false*'
        enva = env0.ensure_expr_is_of_type(exa, T_Boolean); assert enva is env0
        envb = env0.ensure_expr_is_of_type(exb, T_Boolean); # assert envb is env0
        return (envb, envb)

@P("{CONDITION_1} : {var} or {var} is {LITERAL}")
@P("{CONDITION_1} : either {DOTTING} or {DOTTING} is {LITERAL}")
class _:
    def s_cond(cond, env0, asserting):
        [v1, v2, lit] = cond.children
        (t1, env1) = tc_expr(v1, env0); assert env1 is env0
        (t2, env2) = tc_expr(v2, env0); assert env2 is env0
        assert t1 == t2
        env0.assert_expr_is_of_type(lit, t1)
        return (env0, env0)

# ------------------------------------------------------------------------------

@P("{CONDITION_1} : {EX} is also {VAL_DESC}")
@P("{CONDITION_1} : {EX} is never {VAL_DESC}")
@P("{CONDITION_1} : {EX} is not {VALUE_DESCRIPTION}")
@P("{CONDITION_1} : {EX} is {VALUE_DESCRIPTION}")
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

        if str(vd.prod) == '{VALUE_DESCRIPTION} : {VAL_DESC}':
            [val_desc] = vd.children
            assert val_desc.prod.lhs_s == '{VAL_DESC}'
        elif vd.prod.lhs_s == '{VAL_DESC}':
            val_desc = vd
        else:
            val_desc = None
        if val_desc is not None and val_desc.prod.rhs_s in [
            '{LITERAL_ISH}',
            '{LITERAL}',
            '{nonterminal}',
        ]:
            [rhs_ex] = val_desc.children

            (ex_t, env1) = tc_expr(ex, env0)
            (rhs_ex_t, env2) = tc_expr(rhs_ex, env1)
            check_comparison(cond, 'is', ex_t, rhs_ex_t)

        (sub_t, sup_t) = type_bracket_for(vd, env0)
        return env0.with_type_test(ex, copula, [sub_t, sup_t], asserting)

    def d_exec(cond):
        [ex, value_description] = cond.children
        ex_val = EXEC(ex, E_Value)
        matches = value_matches_description(ex_val, value_description)
        if 'not' in cond.prod.rhs_s or 'never' in cond.prod.rhs_s:
            return not matches
        else:
            return matches

@P("{CONDITION_1} : {EX} is neither {VAL_DESC} nor {VAL_DESC} nor {VAL_DESC}")
@P("{CONDITION_1} : {EX} is neither {VAL_DESC} nor {VAL_DESC}")
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

    def d_exec(cond):
        [ex, *vds] = cond.children
        ex_val = EXEC(ex, E_Value)
        for vd in vds:
            matches = value_matches_description(ex_val, vd)
            if matches: return False
        return True

# ------------------------------------------------------------------------------

@P("{VALUE_DESCRIPTION} : {VAL_DESC}")
@P("{VALUE_DESCRIPTION} : either {VAL_DESC_DISJUNCTION}")
@P("{VALUE_DESCRIPTION} : one of {VAL_DESC_DISJUNCTION}")
@P("{VALUE_DESCRIPTION} : {VAL_DESC_DISJUNCTION}")
class _:
    s_tb = s_tb_pass_down

    def d_desc(value_description, value):
        [child] = value_description.children
        return value_matches_description(value, child)

@P("{VAL_DESC_DISJUNCTION} : {VAL_DESC} or {VAL_DESC}")
@P("{VAL_DESC_DISJUNCTION} : {VAL_DESC}, or {VAL_DESC}")
@P("{VAL_DESC_DISJUNCTION} : {VAL_DESC}, {VAL_DESC}, or {VAL_DESC}")
@P("{VAL_DESC_DISJUNCTION} : {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, or {VAL_DESC}")
@P("{VAL_DESC_DISJUNCTION} : {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, or {VAL_DESC}")
@P("{VAL_DESC_DISJUNCTION} : {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, or {VAL_DESC}")
@P("{VAL_DESC_DISJUNCTION} : {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, or {VAL_DESC}")
@P("{VAL_DESC_DISJUNCTION} : {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, or {VAL_DESC}")
@P("{VAL_DESC_DISJUNCTION} : {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, or {VAL_DESC}")
@P("{VAL_DESC_DISJUNCTION} : {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, {VAL_DESC}, or {VAL_DESC}")
class _:
    def s_tb(value_description, env):
        result_sub_t = T_0
        result_sup_t = T_0
        for val_desc in value_description.children:
            (sub_t, sup_t) = type_bracket_for(val_desc, env)
            result_sub_t |= sub_t
            result_sup_t |= sup_t
        return (result_sub_t, result_sup_t)

    def d_desc(value_description, value):
        return any(
            value_matches_description(value, val_desc)
            for val_desc in value_description.children
        )

@P("{VALUE_DESCRIPTION} : {VAL_DESC}, but not {VALUE_DESCRIPTION}")
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

@P("{VAL_DESC} : anything")
class _:
    s_tb = T_host_defined_

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 6 ECMAScript Data Types and Values

#> Within this specification, the notation
#>     “Type(_x_)”
#> is used as shorthand for
#>     “the <em>type</em> of _x_”
#> where “type” refers to the ECMAScript language and specification types
#> defined in this clause.

@P("{TYPE_TEST} : Type({TYPE_ARG}) is Type({TYPE_ARG})")
@P("{TYPE_TEST} : Type({TYPE_ARG}) is not Type({TYPE_ARG})")
class _:
    def s_cond(cond, env0, asserting):
        # Env can't represent the effect of these.
        # If the incoming static types were different,
        # the 'true' env could at least narrow those to their intersection,
        # but the form only appears twice, and in both cases the static types are the same.
        return (env0, env0)

@P("{CONDITION_1} : {var} does not contain Type({TYPE_ARG})")
class _:
    def s_cond(cond, env0, asserting):
        # once, in CreateListFromArrayLike
        [var, type_arg] = cond.children
        env0.assert_expr_is_of_type(var, ListType(T_LangTypeName_))
        return (env0, env0)

# ------------------------------------------------------------------------------

@P("{LITERAL} : {TYPE_NAME}")
class _:
    def s_expr(expr, env0, _):
        [type_name] = expr.children
        return (T_LangTypeName_, env0)

@P("{VAL_DESC} : {LITERAL_ISH}")
@P("{VAL_DESC} : {LITERAL}")
class _:
    s_tb = s_tb_pass_down

    def d_desc(val_desc, value):
        [literal] = val_desc.children
        literal_value = EXEC(literal, E_Value)
        return same_value(value, literal_value)

# ==============================================================================
#@ 6.1 ECMAScript Language Types

#> An <dfn>ECMAScript language type</dfn>
#> corresponds to values that are directly manipulated by an ECMAScript programmer
#> using the ECMAScript language.
#> The ECMAScript language types are
#> Undefined, Null, Boolean, String, Symbol, Number, BigInt, and Object.
#> An <dfn>ECMAScript language value</dfn>
#> is a value that is characterized by an ECMAScript language type.

@P("{VAL_DESC} : an ECMAScript language value")
@P("{LIST_ELEMENTS_DESCRIPTION} : ECMAScript language values")
class _:
    s_tb = T_Tangible_

@P("{LIST_ELEMENTS_DESCRIPTION} : names of ECMAScript Language Types")
class _:
    s_tb = T_LangTypeName_

# ==============================================================================
#@ 6.1.1 The Undefined Type

@dataclass(frozen=True)
class EL_Undefined(EL_Value):
    pass

@P("{LITERAL} : *undefined*")
class _:
    s_tb = T_Undefined

    def s_expr(expr, env0, _):
        return (T_Undefined, env0)

    def d_exec(expr):
        [] = expr.children
        return EL_Undefined()

# ==============================================================================
#@ 6.1.2 The Null Type

@dataclass(frozen=True)
class EL_Null(EL_Value):
    pass

@P("{LITERAL} : *null*")
class _:
    s_tb = T_Null

    def s_expr(expr, env0, _):
        return (T_Null, env0)

    def d_exec(expr):
        [] = expr.children
        return EL_Null()

# ==============================================================================
#@ 6.1.3 The Boolean Type

@dataclass(frozen=True)
class EL_Boolean(EL_Value):
    b: bool

@P("{VAL_DESC} : a Boolean")
class _:
    s_tb = T_Boolean

@P("{LITERAL} : {BOOL_LITERAL}")
class _:
    s_tb = a_subset_of(T_Boolean)

    def s_expr(expr, env0, _):
        return (T_Boolean, env0)

    d_exec = d_exec_pass_down

@P("{BOOL_LITERAL} : *true*")
class _:
    def d_exec(bool_literal):
        [] = bool_literal.children
        return EL_Boolean(True)

@P("{BOOL_LITERAL} : *false*")
class _:
    def d_exec(bool_literal):
        [] = bool_literal.children
        return EL_Boolean(False)

# ==============================================================================
#@ 6.1.4 The String Type

#> The <dfn>String type</dfn> is the set of all ordered sequences
#> of zero or more 16-bit unsigned integer values (“elements”)
#> up to a maximum length of 2<sup>53</sup> - 1 elements.
#> The String type is generally used to represent textual data in a running ECMAScript program,
#> in which case each element in the String is treated as a UTF-16 code unit value.

@dataclass
class EL_String(EL_Value):
    code_units: typing.List[ES_CodeUnit]

    def __init__(self, code_units):
        assert isinstance(code_units, list)
        for code_unit in code_units:
            assert code_unit.isan(ES_CodeUnit)
        self.code_units = code_units

    @staticmethod
    def from_Python_string(string):
        assert isinstance(string, str)
        assert string.isascii() # So I don't have to care about encoding
        return EL_String([
            ES_CodeUnit(ord(char))
            for char in string
        ])

    @staticmethod
    def from_integers(ints):
        return EL_String([
            ES_CodeUnit(i)
            for i in ints
        ])

    def to_Python_String(self):
        return ''.join(
            chr(code_unit.numeric_value) #XXX wrong
            for code_unit in self.code_units
        )

    def __repr__(self):
        chars = self.to_Python_String()
        return f"EL_String({chars!r})"

# ------------------------------------------------

@P("{VAL_DESC} : a String")
@P("{LIST_ELEMENTS_DESCRIPTION} : Strings")
class _:
    s_tb = T_String

    def d_desc(val_desc, value):
        [] = val_desc.children
        return value.isan(EL_String)

@P("{LIST_ELEMENTS_DESCRIPTION} : either Strings or *undefined*")
class _:
    s_tb = T_String | T_Undefined

# ------------------------------------------------------------------------------
#> Each element is regarded as occupying a position within the sequence.
#> These positions are indexed with non-negative integers.
#> The first element (if any) is at index 0, the next element (if any) at index 1, and so on.

@P("{EX} : the code unit at index {EX} within {EX}")
class _:
    def s_expr(expr, env0, _):
        [index_ex, str_ex] = expr.children
        env0.assert_expr_is_of_type(str_ex, T_String)
        env1 = env0.ensure_expr_is_of_type(index_ex, T_MathInteger_)
        return (T_code_unit_, env1)

@P("{EXPR} : the index within {var} of the first such code unit")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_String)
        return (T_MathNonNegativeInteger_, env0)

@P("{EXPR} : {var}'s single code unit element") # todo: element of String
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_String)
        return (T_code_unit_, env1)

@P("{EX} : the first code unit of {var}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_String)
        return (T_code_unit_, env1)

# ------------------------------------------------------------------------------
#> The length of a String is the number of elements (i.e., 16-bit values) within it.
#> The empty String has length zero and therefore contains no elements.

@P("{NUM_COMPARAND} : the length of {var}")
@P("{EX} : the length of {var}")
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
#> is the concatenation of the code units (in order)
#> of each of the arguments (in order).

@P("{MULTILINE_EXPR} : the string-concatenation of:{I_BULLETS}")
class _:
    def s_expr(expr, env0, _):
        [bullets] = expr.children
        # Should check the bullets
        return (T_String, env0)

@P("{EXPR} : the string-concatenation of {EX} and {EX}")
@P("{EXPR} : the string-concatenation of {EX}, {EX}, and {EX}")
@P("{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, and {EX}")
@P("{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, {EX}, and {EX}")
@P("{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, {EX}, {EX}, and {EX}")
@P("{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, and {EX}")
@P("{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, and {EX}")
@P("{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, and {EX}")
@P("{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, and {EX}")
@P("{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, and {EX}")
class _:
    def s_expr(expr, env0, _):
        env1 = env0
        for ex in expr.children:
            env1 = env1.ensure_expr_is_of_type(ex, T_String | T_code_unit_ | ListType(T_code_unit_))
        return (T_String, env1)

    def d_exec(expr):
        code_units = []
        for ex in expr.children:
            val = EXEC(ex, (EL_String, ES_CodeUnit))
            if val.isan(ES_CodeUnit):
                code_units.append(val)
            else:
                code_units.extend(val.code_units)
        return EL_String(code_units)

# ------------------------------------------------------------------------------
#> The phrase "the <dfn>substring</dfn> of _S_ from _inclusiveStart_ to _exclusiveEnd_"
#> (where _S_ is a String value or a sequence of code units and _inclusiveStart_ and _exclusiveEnd_ are integers)
#> denotes the String value consisting of
#> the consecutive code units of _S_
#> beginning at index _inclusiveStart_ and ending immediately before index _exclusiveEnd_
#> (which is the empty String when _inclusiveStart_ = _exclusiveEnd_).
#> If the "to" suffix is omitted, the length of _S_ is used as the value of _exclusiveEnd_.

@P("{EX} : the substring of {var} from {EX} to {EX}")
class _:
    def s_expr(expr, env0, _):
        [s_var, start_var, end_var] = expr.children
        env0.assert_expr_is_of_type(s_var, T_String)
        env1 = env0.ensure_expr_is_of_type(start_var, T_MathNonNegativeInteger_)
        env2 = env1.ensure_expr_is_of_type(end_var, T_MathNonNegativeInteger_)
        return (T_String, env2)

@P("{EX} : the substring of {var} from index {dec_int_lit}")
@P("{EX} : the substring of {var} from {EX}")
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

@P("{STR_LITERAL} : the ASCII word characters")
class _:
    def s_expr(expr, env0, _):
        return (T_String, env0)

# ------------------------------------------------------------------------------
# expressions that return a String value:

def s_expr_String(expr, env0, _):
    return (T_String, env0)

@P("{LITERAL} : {STR_LITERAL}")
class _:
    s_tb = a_subset_of(T_String)
    s_expr = s_expr_String
    d_exec = d_exec_pass_down

@P("{STR_LITERAL} : the empty String")
class _:
    s_expr = s_expr_String

    def d_exec(str_literal):
        [] = str_literal.children
        return EL_String([])

@P("{STR_LITERAL} : {starred_str}")
class _:
    s_expr = s_expr_String
    d_exec = d_exec_pass_down

@P('{STR_LITERAL} : *","* (a comma)')
class _:
    s_expr = s_expr_String

@P("{STR_LITERAL} : {starred_str} ({code_unit_lit} followed by {code_unit_lit})")
class _:
    s_expr = s_expr_String

@P(r'{starred_str} : \* " ( [^"*] | \\ \* )* " \*')
class _:
    def d_exec(starred_str):
        [chars] = starred_str.children
        inner_chars = chars[2:-2]
        true_chars = inner_chars.replace(r'\*', '*')
        return EL_String.from_Python_string(true_chars)

@P("{EX} : the String {var}")
@P("{EXPR} : the String value {SETTABLE}")
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

@P("{EX} : the first {SUM} code units of {var}")
class _:
    def s_expr(expr, env0, _):
        [summ, var] = expr.children
        env0.assert_expr_is_of_type(var, T_String)
        env1 = env0.ensure_expr_is_of_type(summ, T_MathInteger_)
        return (T_String, env1)

@P("{EX} : the remaining {EX} code units of {var}")
@P("{EXPR} : the other {EX} code units of {var}")
class _:
    def s_expr(expr, env0, _):
        [ex, var] = expr.children
        env0.assert_expr_is_of_type(var, T_String)
        env1 = env0.ensure_expr_is_of_type(ex, T_MathInteger_)
        return (T_String, env1)

@P("{EXPR} : the String value consisting solely of {code_unit_lit}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_code_unit_)
        return (T_String, env1)

@P("{EXPR} : the String value consisting of {EX}")
class _:
    def s_expr(expr, env0, _):
        [ex] = expr.children
        env1 = env0.ensure_expr_is_of_type(ex, T_code_unit_ | ListType(T_code_unit_))
        return (T_String, env1)

    def d_exec(expr):
        [ex] = expr.children
        val = EXEC(ex, ES_CodeUnit)
        return EL_String([val])

@P("{EXPR} : the String value that is a copy of {var} with both leading and trailing white space removed")
@P("{EXPR} : the String value that is a copy of {var} with leading white space removed")
@P("{EXPR} : the String value that is a copy of {var} with trailing white space removed")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_String)
        return (T_String, env0)

@P("{EXPR} : the String value that is the same as {var} except that each occurrence of {code_unit_lit} in {var} has been replaced with the six code unit sequence {STR_LITERAL}")
class _:
    def s_expr(expr, env0, _):
        [var, lita, var2, litb] = expr.children
        assert var.children == var2.children
        env1 = env0.ensure_expr_is_of_type(var, T_String)
        return (T_String, env1)

@P("{EXPR} : the String value that is the result of normalizing {var} into the normalization form named by {var} as specified in {h_a}")
class _:
    def s_expr(expr, env0, _):
        [s_var, nf_var, h_a] = expr.children
        env0.assert_expr_is_of_type(s_var, T_String)
        env0.assert_expr_is_of_type(nf_var, T_String)
        return (T_String, env0)

@P("{EXPR} : the String value containing {var} occurrences of {code_unit_lit}")
class _:
    def s_expr(expr, env0, _):
        [n, lit] = expr.children
        env0.assert_expr_is_of_type(lit, T_code_unit_)
        return (T_String, env0)

@P("{EXPR} : the String value that is made from {var} copies of {var} appended together")
class _:
    def s_expr(expr, env0, _):
        [n_var, s_var] = expr.children
        env0.assert_expr_is_of_type(s_var, T_String)
        env1 = env0.ensure_expr_is_of_type(n_var, T_MathInteger_)
        return (T_String, env1)

@P("{EXPR} : the String value consisting of repeated concatenations of {EX} truncated to length {var}")
class _:
    def s_expr(expr, env0, _):
        [ex, var] = expr.children
        env0.assert_expr_is_of_type(ex, T_String)
        env1 = env0.ensure_expr_is_of_type(var, T_MathInteger_)
        return (T_String, env1)

@P("{EXPR} : the String value formed by concatenating all the element Strings of {var} with each adjacent pair of Strings separated with {code_unit_lit}. A comma is not inserted either before the first String or after the last String")
class _:
    def s_expr(expr, env0, _):
        [var, str_literal] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_String))
        return (T_String, env1)

@P("{EXPR} : the String value formed by concatenating all the element Strings of {var} with each adjacent pair of Strings separated with {var}. The {var} String is not inserted either before the first String or after the last String")
class _:
    def s_expr(expr, env0, _):
        [var, sep_var, sep_var2] = expr.children
        assert sep_var.children == sep_var2.children
        env0.assert_expr_is_of_type(sep_var, T_String)
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_String))
        return (T_String, env1)

@P("{EXPR} : the String value whose code units are the elements of the List {var}. If {var} has no elements, the empty String is returned")
class _:
    def s_expr(expr, env0, _):
        [list_var, list_var2] = expr.children
        assert same_source_text(list_var, list_var2)
        env0.assert_expr_is_of_type(list_var, ListType(T_code_unit_))
        return (T_String, env0)

@P("{EXPR} : the implementation-defined list-separator String value appropriate for the host environment's current locale (such as {STR_LITERAL})")
class _:
    def s_expr(expr, env0, _):
        [str_lit] = expr.children
        return (T_String, env0)

# -----------------------------------------
# conditions about the content of a String:

@P("{CONDITION_1} : {EX} contains any code unit more than once")
@P('{CONDITION_1} : {EX} contains any code unit other than *"d"*, *"g"*, *"i"*, *"m"*, *"s"*, *"u"*, *"v"*, or *"y"*')
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_String)
        return (env0, env0)

@P("{CONDITION_1} : {EX} contains a code unit that is not a radix-{var} digit")
class _:
    def s_cond(cond, env0, asserting):
        [svar, rvar] = cond.children
        env0.assert_expr_is_of_type(svar, T_String)
        env0.assert_expr_is_of_type(rvar, T_MathInteger_)
        return (env0, env0)

@P("{CONDITION_1} : {var} starts with {STR_LITERAL}")
class _:
    def s_cond(cond, env0, asserting):
        [var, str_literal] = cond.children
        env0.assert_expr_is_of_type(var, T_String)
        return (env0, env0)

@P("{CONDITION_1} : {var} starts with {STR_LITERAL} followed by {EX} or more decimal digits")
class _:
    def s_cond(cond, env0, asserting):
        [var, str_literal, ex] = cond.children
        env0.assert_expr_is_of_type(var, T_String)
        env0.assert_expr_is_of_type(ex, T_MathNonNegativeInteger_)
        return (env0, env0)

@P("{CONDITION_1} : the first two code units of {var} are either {STR_LITERAL} or {STR_LITERAL}")
class _:
    def s_cond(cond, env0, asserting):
        [var, lita, litb] = cond.children
        env0.assert_expr_is_of_type(var, T_String)
        env0.assert_expr_is_of_type(lita, T_String)
        env0.assert_expr_is_of_type(litb, T_String)
        return (env0, env0)

# --------------------------------------------
# conditions involving multiple String values:

@P("{CONDITION_1} : {var} and {var} have the same length and the same code units in the same positions")
class _:
    def s_cond(cond, env0, asserting):
        # occurs once, in SameValueNonNumber
        [vara, varb] = cond.children
        enva = env0.ensure_expr_is_of_type(vara, T_String); assert enva is env0
        envb = env0.ensure_expr_is_of_type(varb, T_String); # assert envb is env0
        return (envb, envb)

# ------------------------------------------------------------------------------
# going from a String value to some other type of value:

@P("{EXPR} : a List whose elements are the code units that are the elements of {var}")
@P("{EXPR} : a List consisting of the sequence of code units that are the elements of {var}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_String)
        return (ListType(T_code_unit_), env0)

@P("{EXPR} : the result of interpreting each of {var}'s 16-bit elements as a Unicode BMP code point. UTF-16 decoding is not applied to the elements")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_String)
        return (T_Unicode_code_points_, env0)

@P("{EXPR} : the sequence of code points resulting from interpreting each of the 16-bit elements of {var} as a Unicode BMP code point. UTF-16 decoding is not applied to the elements")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_String)
        return (T_Unicode_code_points_, env0)

    def d_exec(expr):
        [var] = expr.children
        string = EXEC(var, EL_String)
        # This breaks encapsulation on EL_String *and* ES_UnicodeCodePoints:
        text = ''.join(
            chr(code_unit.numeric_value)
            for code_unit in string.code_units
        )
        return ES_UnicodeCodePoints(text)

@P("{EXPR} : the integer value that is represented by {var} in radix-{var} notation, using the letters <b>A</b> through <b>Z</b> and <b>a</b> through <b>z</b> for digits with values 10 through 35")
class _:
    def s_expr(expr, env0, _):
        [zvar, rvar] = expr.children
        env0.assert_expr_is_of_type(zvar, T_String)
        env0.assert_expr_is_of_type(rvar, T_MathInteger_)
        return (T_MathInteger_, env0)

# ------------------------------------------------------------------------------
# comparing a String value to a nonterminal:

# for 19.2.4 parseFloat
@P("{EXPR} : the longest prefix of {var} that satisfies the syntax of a {nonterminal}, which might be {var} itself. If there is no such prefix, return {NUMBER_LITERAL}")
class _:
    def s_expr(expr, env0, _):
        [var1, nont, var2, lit] = expr.children
        assert same_source_text(var1, var2)
        env0.assert_expr_is_of_type(var1, T_Unicode_code_points_)
        proc_add_return(env0, T_Number, lit)
        return (T_Unicode_code_points_, env0)

# ==============================================================================
#@ 6.1.5 The Symbol Type

@dataclass
class EL_Symbol(EL_Value):
    description: EL_Undefined | EL_String

@P("{VAL_DESC} : a Symbol")
class _:
    s_tb = T_Symbol

    def d_desc(val_desc, value):
        [] = val_desc.children
        return value.isan(EL_Symbol)

@P("{LITERAL} : {atat_word}")
class _:
    def s_expr(expr, env0, _):
        return (T_Symbol, env0)

#> Each Symbol value immutably holds
#> an associated value called [[Description]]
#> that is either *undefined* or a String value.

@P("{EXPR} : a new Symbol whose {DSBN} is {var}")
class _:
    def s_expr(expr, env0, _):
        [dsbn, var] = expr.children
        assert dsbn.source_text() == '[[Description]]'
        env0.assert_expr_is_of_type(var, T_String | T_Undefined)
        return (T_Symbol, env0)

@P("{EXPR} : {var}'s {DSBN} value")
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

@dataclass(frozen=True)
class EL_Number(EL_Value):
    def __init__(self, val):
        if val in [
            'not a number',
            'negative infinity',
            'positive infinity',
        ]:
            pass

        elif (
            isinstance(val, tuple)
            and len(val) == 2
            and val[0] in ['-', '+']
            and val[1] >= 0
        ):
            pass

        else:
            assert 0, val

        object.__setattr__(self, 'val', val)

# --------------

@P("{VAL_DESC} : a Number")
class _:
    s_tb = T_Number

    def d_desc(val_desc, value):
        [] = val_desc.children
        return value.isan(EL_Number)

# --------------
# make a Number:

@P("{NUMBER_LITERAL} : {starred_neg_infinity_lit}{h_sub_fancy_f}")
class _:
    s_tb = T_NegInfinityNumber_

    def s_expr(expr, env0, _):
        return (T_NegInfinityNumber_, env0)

@P("{NUMBER_LITERAL} : {starred_pos_infinity_lit}{h_sub_fancy_f}")
class _:
    s_tb = T_PosInfinityNumber_

    def s_expr(expr, env0, _):
        return (T_PosInfinityNumber_, env0)

@P("{NUMBER_LITERAL} : {starred_nan_lit}")
@P("{NUMBER_LITERAL} : the *NaN* Number value")
class _:
    s_tb = T_NaN_Number_

    def s_expr(expr, env0, _):
        return (T_NaN_Number_, env0)

    def d_exec(expr):
        return EL_Number('not a number')

@P("{NUMBER_LITERAL} : *0.5*{h_sub_fancy_f}")
@P("{NUMBER_LITERAL} : *-0.5*{h_sub_fancy_f}")
class _:
    def s_expr(expr, env0, _):
        return (T_NonIntegralFiniteNumber_, env0)

@P("{NUMBER_LITERAL} : {starred_int_lit}{h_sub_fancy_f}")
class _:
    s_tb = a_subset_of(T_IntegralNumber_)

    def s_expr(expr, env0, _):
        [_, _] = expr.children
        return (T_IntegralNumber_, env0)

@P("{EXPR} : the Number value that corresponds to {var}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_IEEE_binary32_ | T_IEEE_binary64_ | T_MathInteger_)
        return (T_Number, env1)

@P("{EX} : the Number value for {EX}")
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

@P("{EXPR} : the result of negating {var}; that is, compute a Number with the same magnitude but opposite sign")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_Number)
        return (T_Number, env0)

@P("{EXPR} : the smallest (closest to -∞) integral Number value that is not less than {var}")
@P("{EXPR} : the greatest (closest to +∞) integral Number value that is not greater than {var}")
@P("{EXPR} : the integral Number closest to {var}, preferring the Number closer to +∞ in the case of a tie")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_Number)
        return (T_Number, env0)

@P("{EXPR} : the largest integral Number {DEFVAR} (closest to +\u221e) such that {CONDITION_1}")
class _:
    def s_expr(expr, env0, _):
        [defvar, cond] = expr.children
        env1 = env0.plus_new_entry(defvar, T_IntegralNumber_)
        (t_env, _) = tc_cond(cond, env1)
        return (T_IntegralNumber_, t_env)

@P("{EXPR} : the integral Number nearest {var} in the direction of *+0*{h_sub_fancy_f}")
class _:
    def s_expr(expr, env0, _):
        [var, _] = expr.children
        env0.assert_expr_is_of_type(var, T_Number)
        return (T_Number, env0)

@P("{EXPR} : an implementation-approximated Number value representing {EXPR}")
class _:
    def s_expr(expr, env0, _):
        [ex] = expr.children
        env0.assert_expr_is_of_type(ex, T_MathReal_)
        return (T_Number, env0)

@P("{EXPR} : the result of converting {var} to IEEE 754-2019 binary32 format using roundTiesToEven mode")
@P("{EXPR} : the result of converting {var} to IEEE 754-2019 binary64 format")
@P("{EXPR} : the ECMAScript Number value corresponding to {var}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_Number)
        # XXX The intermediates are not really T_Number
        return (T_Number, env0)

# -------------------------
# conditions on one Number:

@P("{CONDITION_1} : {var} is finite")
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

@P("{CONDITION_1} : {var} is not finite")
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

@P("{CONDITION_1} : {var} is finite and is neither {NUMBER_LITERAL} nor {NUMBER_LITERAL}")
class _:
    def s_cond(cond, env0, asserting):
        [var, lita, litb] = cond.children
        env1 = env0.ensure_expr_is_of_type(var, T_FiniteNumber_)
        env1.assert_expr_is_of_type(lita, T_FiniteNumber_)
        env1.assert_expr_is_of_type(litb, T_FiniteNumber_)
        return (env1, env1)

# -------------------------------
# conditions on multiple Numbers:

@P("{CONDITION_1} : {var} and {var} are both finite")
class _:
    def s_cond(cond, env0, asserting):
        [a, b] = cond.children
        (a_t_env, a_f_env) = env0.with_type_test(a, 'is a', T_FiniteNumber_, asserting)
        (b_t_env, b_f_env) = env0.with_type_test(b, 'is a', T_FiniteNumber_, asserting)
        return (
            env_and(a_t_env, b_t_env),
            env_or(a_f_env, b_f_env)
        )

@P("{CONDITION_1} : {var} and {var} are finite")
@P("{CONDITION_1} : {var} and {var} are finite and non-zero")
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

# ----------------------------------------------
#> In this specification, the phrase "the Number value for _x_"
#> where _x_ represents an exact real mathematical quantity
#> (which might even be an irrational number such as π)
#> means a Number value chosen in the following manner. ...

def the_Number_value_for(mathnum: ES_Mathnum):
    max_safe_integer = 2**53 - 1
    if isinstance(mathnum.val, int):
        if 0 <= mathnum.val < max_safe_integer:
            return EL_Number(('+', mathnum.val))
        
    if mathnum.val >= 2**1024:
        return EL_Number('positive infinity')

    assert NYI, mathnum

# -----------------------------

@P("{EXPR} : a List whose elements are the 4 bytes that are the result of converting {var} to IEEE 754-2019 binary32 format using roundTiesToEven mode. The bytes are arranged in little endian order. If {var} is *NaN*, {var} may be set to any implementation chosen IEEE 754-2019 binary32 format Not-a-Number encoding. An implementation must always choose the same encoding for each implementation distinguishable *NaN* value")
@P("{EXPR} : a List whose elements are the 8 bytes that are the IEEE 754-2019 binary64 format encoding of {var}. The bytes are arranged in little endian order. If {var} is *NaN*, {var} may be set to any implementation chosen IEEE 754-2019 binary64 format Not-a-Number encoding. An implementation must always choose the same encoding for each implementation distinguishable *NaN* value")
class _:
    def s_expr(expr, env0, _):
        var = expr.children[0]
        env1 = env0.ensure_expr_is_of_type(var, T_Number)
        return (ListType(T_MathInteger_), env1)

# ----------------------------------------------
# Treating an integral Number like a bit-string:

@P("{EXPR} : the result of applying bitwise complement to {var}. The mathematical value of the result is exactly representable as a 32-bit two's complement bit string")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_IntegralNumber_)
        return (T_IntegralNumber_, env0)

@P("{EX} : the result of left shifting {var} by {var} bits. The mathematical value of the result is exactly representable as a 32-bit two's complement bit string")
@P("{EXPR} : the result of performing a sign-extending right shift of {var} by {var} bits. The most significant bit is propagated. The mathematical value of the result is exactly representable as a 32-bit two's complement bit string")
@P("{EXPR} : the result of performing a zero-filling right shift of {var} by {var} bits. Vacated bits are filled with zero. The mathematical value of the result is exactly representable as a 32-bit unsigned bit string")
class _:
    def s_expr(expr, env0, _):
        [avar, bvar] = expr.children
        env1 = env0.ensure_expr_is_of_type(avar, T_IntegralNumber_)
        env1.assert_expr_is_of_type(bvar, T_MathInteger_)
        return (T_IntegralNumber_, env1)

@P("{EXPR} : the number of leading zero bits in the unsigned 32-bit binary representation of {var}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_IntegralNumber_)
        return (T_MathNonNegativeInteger_, env0)

# ------------------------------------------------------------------------------

@P("{VAL_DESC} : an IEEE 754-2019 binary32 NaN value")
class _:
    s_tb = a_subset_of(T_IEEE_binary32_)

@P("{VAL_DESC} : an IEEE 754-2019 binary64 NaN value")
class _:
    s_tb = a_subset_of(T_IEEE_binary64_)

# ==============================================================================
#@ 6.1.6.2 The BigInt Type

@P("{VAL_DESC} : a BigInt")
@P("{LIST_ELEMENTS_DESCRIPTION} : BigInts")
class _:
    s_tb = T_BigInt

@P("{LITERAL} : {BIGINT_LITERAL}")
class _:
    s_tb = a_subset_of(T_BigInt)
    s_expr = s_expr_pass_down

@P("{BASE} : {BIGINT_LITERAL}")
class _:
    s_expr = s_expr_pass_down

@P("{BIGINT_LITERAL} : {starred_int_lit}{h_sub_fancy_z}")
class _:
    def s_expr(expr, env0, _):
        [_, _] = expr.children
        return (T_BigInt, env0)

@P("{EXPR} : the BigInt value that corresponds to {var}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_MathInteger_)
        return (T_BigInt, env0)

@P("{EX} : the BigInt value for {EX}")
class _:
    def s_expr(expr, env0, _):
        [ex] = expr.children
        env0.assert_expr_is_of_type(ex, T_MathInteger_)
        return (T_BigInt, env0)

@P("{EXPR} : the String value consisting of the representation of {var} using radix {var}")
class _:
    def s_expr(expr, env0, _):
        [x_var, radix_var] = expr.children
        env0.assert_expr_is_of_type(x_var, T_BigInt)
        env0.assert_expr_is_of_type(radix_var, T_MathInteger_)
        return (T_String, env0)

# ==============================================================================
#@ 6.1.7 The Object Type


# --------------------------------

@P("{VAL_DESC} : an Object")
@P("{LIST_ELEMENTS_DESCRIPTION} : Objects")
class _:
    s_tb = T_Object

@P("{LIST_ELEMENTS_DESCRIPTION} : either Objects or Symbols")
class _:
    s_tb = T_Object | T_Symbol

# ------------------------------------------------------------------------------
#> An Object is logically a collection of properties.
#> Each property is either a data property, or an accessor property:
#>  -- A <dfn>data property</dfn> associates a key value with
#>     an ECMAScript language value and a set of Boolean attributes.
#>  -- An <dfn>accessor property</dfn> associates a key value with
#>     one or two accessor functions, and a set of Boolean attributes.
#>     The accessor functions are used to store or retrieve
#>     an ECMAScript language value that is associated with the property.

@dataclass # not frozen
class Property: # ES_Property(ES_Value) ?
    pass

@dataclass # not frozen
class EL_Object(EL_Value):
    properties: typing.List[Property]

@P("{VAL_DESC} : an? {PROPERTY_KIND} property")
class _:
    def s_tb(val_desc, env):
        [kind] = val_desc.children
        t = {
            'accessor': T_accessor_property_,
            'data'    : T_data_property_,
        }[kind.source_text()]
        return t

# ------------------------------------------------------------------------------
#> Properties are identified using key values.
#> A <dfn>property key</dfn> value is either an ECMAScript String value or a Symbol value.
#> All String and Symbol values, including the empty String, are valid as property keys.

@P("{VAL_DESC} : a property key")
@P("{LIST_ELEMENTS_DESCRIPTION} : property keys")
class _:
    s_tb = T_String | T_Symbol

# ------------------------------------------------------------------------------
#> A <dfn>property name</dfn> is a property key that is a String value.

@P("{EXPR} : the String value of the property name")
class _:
    def s_expr(expr, env0, _):
        # property of the Global Object
        # todo: make that explicit
        [] = expr.children
        return (T_String, env0)

# ------------------------------------------------------------------------------
#> An <dfn>integer index</dfn>
#> is a String-valued property key
#> that is a canonical numeric string
#> and whose numeric value is either *+0*<sub>𝔽</sub>
#> or a positive integral Number ≤ 𝔽(2<sup>53</sup> - 1).

@P("{VAL_DESC} : an integer index")
class _:
    s_tb = a_subset_of(T_String)

#> An <dfn>array index</dfn>
#> is an integer index whose numeric value _i_
#> is in the range <emu-eqn>*+0*<sub>𝔽</sub> ≤ _i_ &lt; 𝔽(2<sup>32</sup> - 1)</emu-eqn>.

@P("{VAL_DESC} : an array index")
class _:
    s_tb = a_subset_of(T_String)

# ------------------------------------------------------------------------------
# (forms involving the properties of an object)

@P("{VAL_DESC} : an extensible object that does not have a {starred_str} own property")
class _:
    s_tb = a_subset_of(T_Object)

@P("{CONDITION_1} : {var} does not have an own property with key {var}")
@P("{CONDITION_1} : {var} does not currently have a property {var}")
class _:
    def s_cond(cond, env0, asserting):
        [obj_var, key_var] = cond.children
        env0.assert_expr_is_of_type(obj_var, T_Object)
        env0.assert_expr_is_of_type(key_var, T_String | T_Symbol)
        return (env0, env0)

@P("{EXPR} : {var}'s own property whose key is {var}")
class _:
    def s_expr(expr, env0, _):
        [obj_var, key_var] = expr.children
        env0.assert_expr_is_of_type(obj_var, T_Object)
        env0.assert_expr_is_of_type(key_var, T_String | T_Symbol)
        return (T_property_, env0)

@P("{CONDITION_1} : The mathematical value of {var}'s {starred_str} property is {EX}")
class _:
    def s_cond(cond, env0, asserting):
        [var, prop_name, ex] = cond.children
        env0.assert_expr_is_of_type(var, T_Object)
        env0.assert_expr_is_of_type(ex, T_MathInteger_)
        return (env0, env0)

@P("{EACH_THING} : own property key {DEFVAR} of {var} such that {CONDITION}, in ascending numeric index order")
@P("{EACH_THING} : own property key {DEFVAR} of {var} such that {CONDITION}, in ascending chronological order of property creation")
@P("{EACH_THING} : own property key {DEFVAR} of {var} such that {CONDITION}, in descending numeric index order")
class _:
    def s_nv(each_thing, env0):
        [loop_var, obj_var, condition] = each_thing.children
        env0.assert_expr_is_of_type(obj_var, T_Object)
        env1 = env0.plus_new_entry(loop_var, T_String | T_Symbol)
        (tenv, fenv) = tc_cond(condition, env1)
        return tenv

@P("{COMMAND} : Remove the own property with name {var} from {var}.")
class _:
    def s_nv(anode, env0):
        [name_var, obj_var] = anode.children
        env0.assert_expr_is_of_type(name_var, T_String | T_Symbol)
        env0.assert_expr_is_of_type(obj_var, T_Object)
        return env0

# ==============================================================================
#@ 6.1.7.1 Property Attributes

@P("{COMMAND} : Create an own {PROPERTY_KIND} property named {var} of object {var} whose {dsb_word}, {dsb_word}, {dsb_word}, and {dsb_word} attributes are set to the value of the corresponding field in {var} if {var} has that field, or to the attribute's {h_emu_xref} otherwise.")
class _:
    def s_nv(anode, env0):
        [kind, name_var, obj_var, *dsbw_, desc_var, desc_var2, emu_xref] = anode.children
        assert desc_var.source_text() == desc_var2.source_text()
        env0.ensure_expr_is_of_type(name_var, T_String | T_Symbol)
        env0.assert_expr_is_of_type(obj_var, T_Object)
        env0.assert_expr_is_of_type(desc_var, T_Property_Descriptor)
        return env0

@P("{SETTABLE} : {var}'s {DSBN} attribute")
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

@P("{EXPR} : an Iterator object ({h_emu_xref}) whose `next` method iterates over all the String-valued keys of enumerable properties of {var}. The iterator object is never directly accessible to ECMAScript code. The mechanics and order of enumerating the properties is not specified but must conform to the rules specified below")
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

@P("{CONDITION_1} : {var} has an? {DSBN} internal method")
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

# ------------------------------------------------------------------------------
#> Internal slots correspond to internal state
#> that is associated with objects
#> and used by various ECMAScript specification algorithms.

@P("{VAL_DESC} : an internal slot name")
@P("{LIST_ELEMENTS_DESCRIPTION} : internal slot names")
@P("{LIST_ELEMENTS_DESCRIPTION} : names of internal slots")
class _:
    s_tb = T_SlotName_

# ------------------------------------------------------------------------------
#> Internal methods and internal slots are identified within this specification
#> using names enclosed in double square brackets [[ ]].

@P("{EX} : {DSBN}")
class _:
    def s_expr(expr, env0, _):
        [dsbn] = expr.children
        return (T_SlotName_, env0)

# ------------------------------------------------------------------------------

@P("{VAL_DESC} : an Object that has a {dsb_word} internal slot")
class _:
    def s_tb(val_desc, env):
        [dsb_word] = val_desc.children
        return tb_for_object_with_slot(dsb_word)

@P("{CONDITION_1} : {var} has an? {DSBN} internal slot")
@P("{CONDITION_1} : {var} also has a {DSBN} internal slot")
class _:
    def s_cond(cond, env0, asserting):
        [var, dsbn] = cond.children
        env0.assert_expr_is_of_type(var, T_Object)
        tb = tb_for_object_with_slot(dsbn)
        return env0.with_type_test(var, 'is a', tb, asserting)

@P("{CONDITION_1} : {var} has {DSBN} and {DSBN} internal slots")
class _:
    def s_cond(cond, env0, asserting):
        [var, dsbna, dsbnb] = cond.children
        env0.assert_expr_is_of_type(var, T_Object)
        tba = tb_for_object_with_slot(dsbna)
        tbb = tb_for_object_with_slot(dsbnb)
        if tba == tbb:
            tb = tba
        else:
            # get %TypedArray%.prototype.length says:
            # Assert: _O_ has [[ViewedArrayBuffer]] and [[ArrayLength]] internal slots.
            # [[ViewedArrayBuffer]] implies TypedArray or DataView
            # [[ArrayLength]] only implies TypeArray
            assert tba == T_TypedArray_object_ | T_DataView_object_
            assert tbb == T_TypedArray_object_
            # In order to satisfy both,
            tb = T_TypedArray_object_
            # (Mind you, the Assert is kind of pointless.)
        return env0.with_type_test(var, 'is a', tb, asserting)

@P("{CONDITION_1} : {var} has an? {DSBN} or {DSBN} internal slot")
class _:
    def s_cond(cond, env0, asserting):
        [var, dsbna, dsbnb] = cond.children
        env0.assert_expr_is_of_type(var, T_Object)
        assert dsbna.source_text() == '[[StringData]]'
        assert dsbnb.source_text() == '[[NumberData]]'
        # If/when we represent Number exotic object in type hier, then:
        # return env0.with_type_test(var, 'is a', T_String_exotic_object_ | T_Number_exotic_object_, asserting)
        return (env0, env0)

@P("{CONDITION_1} : {var} has an? {DSBN} internal slot whose value is an Object")
class _:
    def s_cond(cond, env0, asserting):
        [var, dsbn] = cond.children
        env0.assert_expr_is_of_type(var, T_Object) # more specific?
        return (env0, env0)

@P("{CONDITION_1} : {var} does not have an? {DSBN} internal slot")
class _:
    def s_cond(cond, env0, asserting):
        [var, dsbn] = cond.children
        env1 = env0.ensure_expr_is_of_type(var, T_Object)
        tb = tb_for_object_with_slot(dsbn)
        return env1.with_type_test(var, 'isnt a', tb, asserting)

@P("{CONDITION_1} : {var} does not have an? {var} internal slot")
class _:
    def s_cond(cond, env0, asserting):
        [obj_var, slotname_var] = cond.children
        env0.assert_expr_is_of_type(obj_var, T_Object)
        env0.assert_expr_is_of_type(slotname_var, T_SlotName_)
        return (env0, env0)

@P("{CONDITION_1} : {var} does not have either a {DSBN} or an {DSBN} internal slot")
class _:
    def s_cond(cond, env0, asserting):
        [var, dsbna, dsbnb] = cond.children
        env0.assert_expr_is_of_type(var, T_Object)
        tba = tb_for_object_with_slot(dsbna)
        tbb = tb_for_object_with_slot(dsbnb)
        assert isinstance(tba, Type)
        assert isinstance(tbb, Type)
        tb = tba | tbb
        return env0.with_type_test(var, 'isnt a', tb, asserting)

@P("{CONDITION_1} : {var} has all of the internal slots of a For-In Iterator Instance ({h_emu_xref})")
class _:
    def s_cond(cond, env0, asserting):
        [var, emu_xref] = cond.children
        env0.assert_expr_is_of_type(var, T_Object)
        return (env0, env0)

    # explicit-exotics:
@P("{EX} : the internal slots listed in {h_emu_xref}")
class _:
    def s_expr(expr, env0, _):
        # XXX really, the *names* of the internal slots...
        return (ListType(T_SlotName_), env0)

#> All objects have an internal slot named [[PrivateElements]],
#> which is a List of PrivateElements.
#> This List represents the values of
#> the private fields, methods, and accessors for the object.
#> Initially, it is an empty List.

declare_isom(T_Object, 'must have', 'slot', '[[PrivateElements]]', ListType(T_PrivateElement))

#> <emu-xref href="#table-essential-internal-methods"></emu-xref>
#> summarizes the <em>essential internal methods</em>
#> used by this specification
#> that are applicable to all objects created or manipulated by ECMAScript code.
#> Every object must have algorithms for all of the essential internal methods.
#> However, all objects do not necessarily use the same algorithms for those methods.

@P("{COMMAND} : Set {var}'s essential internal methods to the default ordinary object definitions specified in {h_emu_xref}.")
class _:
    def s_nv(anode, env0):
        [var, emu_xref] = anode.children
        env1 = env0.ensure_expr_is_of_type(var, T_Object)
        return env1

@P("{COMMAND} : Set {var}'s essential internal methods to the definitions specified in {h_emu_xref}.")
class _:
    def s_nv(anode, env0):
        [var, emu_xref] = anode.children
        assert emu_xref.source_text() == '<emu-xref href="#sec-module-namespace-exotic-objects"></emu-xref>'
        env1 = env0.ensure_expr_is_of_type(var, T_module_namespace_exotic_object_)
        return env1

@P("{COMMAND} : Set {var}'s essential internal methods, except for {DSBN} and {DSBN}, to the definitions specified in {h_emu_xref}.")
class _:
    def s_nv(anode, env0):
        [var, _, _, emu_xref] = anode.children
        assert emu_xref.source_text() == '<emu-xref href="#sec-proxy-object-internal-methods-and-internal-slots"></emu-xref>'
        return env0.with_expr_type_narrowed(var, T_Proxy_exotic_object_)

@P("{COMMAND} : Set {DOTTING} as described in {h_emu_xref}.")
@P("{COMMAND} : Set {DOTTING} as specified in {h_emu_xref}.")
@P("{COMMAND} : Set {DOTTING} to the definition specified in {h_emu_xref}.")
class _:
    def s_nv(anode, env0):
        [dotting, emu_xref] = anode.children

        mo = re.fullmatch(r'<emu-xref href="#([^"<>]+)"></emu-xref>', emu_xref.source_text())
        sec_id = mo.group(1)
        implied_base_t = {
            # 10.2.*
            'sec-ecmascript-function-objects-call-thisargument-argumentslist'                        : T_ECMAScript_function_object_,
            'sec-ecmascript-function-objects-construct-argumentslist-newtarget'                      : T_constructor_object_,

            # 10.3.2
            'sec-built-in-function-objects-construct-argumentslist-newtarget'                        : T_constructor_object_,

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
            'sec-typedarray-getownproperty'                                                          : T_TypedArray_object_,
            'sec-typedarray-hasproperty'                                                             : T_TypedArray_object_,
            'sec-typedarray-defineownproperty'                                                       : T_TypedArray_object_,
            'sec-typedarray-get'                                                                     : T_TypedArray_object_,
            'sec-typedarray-set'                                                                     : T_TypedArray_object_,
            'sec-typedarray-delete'                                                                  : T_TypedArray_object_,
            'sec-typedarray-ownpropertykeys'                                                         : T_TypedArray_object_,

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
        elif implied_base_t == T_constructor_object_:
            # T_constructor_object_ is an odd case
            assert curr_base_t in [T_ECMAScript_function_object_, T_built_in_function_object_]
            return env1.with_expr_type_replaced(base_var, implied_base_t)
        else:
            add_pass_error_re_wrong_type(base_var, curr_base_t, implied_base_t)
            return env1.with_expr_type_replaced(base_var, implied_base_t)

# ------------------------------------------------------------------------------
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

@P("{VAL_DESC} : an ordinary object")
class _:
    s_tb = a_subset_of(T_Object)

@P("{VAL_DESC} : an ordinary, extensible object")
@P("{VAL_DESC} : an ordinary, extensible object with no non-configurable properties")
class _:
    s_tb = a_subset_of(T_Object)

@P("{VAL_DESC} : an extensible ordinary object with no own properties")
class _:
    s_tb = a_subset_of(T_Object)

@P("{CONDITION_1} : {DOTTING} is not the ordinary object internal method defined in {h_emu_xref}")
class _:
    def s_cond(cond, env0, asserting):
        [dotting, emu_xref] = cond.children
        env0.assert_expr_is_of_type(dotting, T_proc_)
        return (env0, env0)

#> An <dfn>exotic object</dfn> is an object that is not an ordinary object.

#> A <dfn>function object</dfn> is an object that supports the [[Call]] internal method.
#> A <dfn>constructor</dfn> is an object that supports the [[Construct]] internal method.

@P("{VAL_DESC} : a function object")
@P("{VAL_DESC} : a callable Object")
class _:
    s_tb = T_function_object_

@P("{VAL_DESC} : a constructor")
class _:
    s_tb = T_constructor_object_

@P("{VAL_DESC} : a {h_emu_xref}")
class _:
    def s_tb(val_desc, env):
        [emu_xref] = val_desc.children
        if emu_xref.source_text() == '<emu-xref href="#sec-built-in-function-objects">built-in function object</emu-xref>':
            return a_subset_of(T_function_object_)
        else:
            assert 0, emu_xref

# ------

# Creating objects:

@P("{EXPR} : a newly created object with an internal slot for each name in {var}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_SlotName_))
        return (T_Object, env1)

@P("{EXPR} : a new {cap_word} object whose {dsb_word} internal slot is set to {var}. See {h_emu_xref} for a description of {cap_word} objects")
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
#> the intrinsic object, associated with the current realm,
#> corresponding to the name.

@P("{LITERAL_ISH} : {percent_word}")
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

@P("{EXPR} : the intrinsic function {percent_word}")
class _:
    def s_expr(expr, env0, _):
        [percent_word] = expr.children
        return (T_function_object_, env0)

@P("{EXPR} : {var}'s intrinsic object named {var}")
class _:
    def s_expr(expr, env0, _):
        [r_var, n_var] = expr.children
        env0.assert_expr_is_of_type(r_var, T_Realm_Record)
        env0.assert_expr_is_of_type(n_var, T_String)
        return (T_Object, env0)

    # 10.1.{13,14}
@P("{CONDITION_1} : {var} is this specification's name of an intrinsic object. The corresponding object must be an intrinsic that is intended to be used as the {DSBN} value of an object")
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

@dataclass
class ES_List(ES_Value):
    _elements: typing.List

    def __repr__(self):
        x = ', '.join(
            repr(el)
            for el in self._elements
        )
        return f"ES_List({x})"

    # make:

    def copy(self):
        return ES_List(self._elements[:])

    @staticmethod
    def concat(*lists):
        all_elements = []
        for alist in lists:
            assert alist.isan(ES_List)
            all_elements.extend(alist._elements)
        return ES_List(all_elements)

    # modify:

    def append_one(self, element):
        assert element.isan(E_Value)
        self._elements.append(element)

    def append_many(self, other):
        assert other.isan(ES_List)
        self._elements.extend(other._elements)

    # iterate:
    
    def each(self, item_nature_s):
        for element in self._elements:
            # assert element is_blah item_nature_s
            yield element

    # query:

    def is_empty(self):
        return (len(self._elements) == 0)

    def number_of_elements(self):
        return ES_Mathnum(len(self._elements))

    def elements(self):
        return iter(self._elements)

    def contains(self, value):
        return any(
            same_value(element, value)
            for element in self._elements
        )

    def contains_an_element_satisfying(self, predicate):
        return any(
            predicate(element)
            for element in self._elements
        )

    def number_of_occurrences_of(self, value):
        return len([
            element
            for element in self._elements
            if same_value(element, value)
        ])

    def contains_any_duplicates(self):
        for i in range(0, len(self._elements)):
            ei = self._elements[i]
            for j in range(0, i):
                ej = self._elements[j]
                if same_value(ei, ej):
                    return True
        return False

    def has_any_element_in_common_with(self, other):
        for se in self._elements:
            for oe in other._elements:
                if same_value(se, oe):
                    return True
        return False

# ------------------------------------------------------------------------------

@P("{VAL_DESC} : a possibly empty List")
class _:
    s_tb = T_List

@P("{VAL_DESC} : a List of {LIST_ELEMENTS_DESCRIPTION}")
class _:
    def s_tb(val_desc, env):
        [led] = val_desc.children
        (sub_t, sup_t) = type_bracket_for(led, env)
        return (ListType(sub_t), ListType(sup_t))

@P("{VAL_DESC} : a List of {LIST_ELEMENTS_DESCRIPTION} with length equal to {EX}")
class _:
    def s_tb(val_desc, env):
        [led, ex] = val_desc.children
        env.assert_expr_is_of_type(ex, T_MathInteger_)
        (led_sub_t, led_sup_t) = type_bracket_for(led, env)
        return a_subset_of(ListType(led_sup_t))
        # inexact because of length restriction

@P("{VAL_DESC} : a non-empty List of {LIST_ELEMENTS_DESCRIPTION}")
class _:
    def s_tb(val_desc, env):
        [led] = val_desc.children
        (led_sub_t, led_sup_t) = type_bracket_for(led, env)
        return a_subset_of(ListType(led_sup_t))
        # inexact because of 'non-empty'

# ------------------------------------------------------------------------------
# make a List:

@P("{EXPR} : a new empty List")
@P("{EX} : « »")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (ListType(T_0), env0)

    def d_exec(expr):
        [] = expr.children
        return ES_List([])

@P("{EX} : « {EXLIST} »")
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

    def d_exec(expr):
        [exlist] = expr.children
        values = EXEC(exlist, list)
        return ES_List(values)

@P("{EXPR} : a List whose sole element is {EX}")
class _:
    def s_expr(expr, env0, _):
        [element_expr] = expr.children
        (element_type, env1) = tc_expr(element_expr, env0); assert env1.equals(env0)
        return (ListType(element_type), env0)

    def d_exec(expr):
        [element_ex] = expr.children
        element_value = EXEC(element_ex, E_Value)
        return ES_List([element_value])

@P("{EXPR} : a copy of the List {var}")
@P("{EXPR} : a List whose elements are the elements of {var}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        t = env0.assert_expr_is_of_type(var, T_List)
        return (t, env0)

@P("{EXPR} : the list-concatenation of {EX} and {EX}")
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

    def d_exec(expr):
        [vara, varb] = expr.children
        lista = EXEC(vara, ES_List)
        listb = EXEC(varb, ES_List)
        return ES_List.concat(lista, listb)

@P("{EXPR} : the list-concatenation of {EX}, {EX}, and {EX}")
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

    def d_exec(expr):
        [vara, varb, varc] = expr.children
        lista = EXEC(vara, ES_List)
        listb = EXEC(varb, ES_List)
        listc = EXEC(varc, ES_List)
        return ES_List.concat(lista, listb, listc)

@P("{EXPR} : a List whose elements are the elements of {var} ordered as if an Array of the same values had been sorted using {percent_word} using {LITERAL} as {var}")
class _:
    def s_expr(expr, env0, _):
        [var, _, _, _] = expr.children
        (t, env1) = tc_expr(var, env0); assert env1 is env0
        assert t.is_a_subtype_of_or_equal_to(T_List)
        return (t, env0)

@P("{EXPR} : a List whose elements are the first {var} elements of {EX}")
class _:
    def s_expr(expr, env0, _):
        [nvar, listvar] = expr.children
        env0.assert_expr_is_of_type(nvar, T_MathNonNegativeInteger_)
        (t, env1) = tc_expr(listvar, env0); assert env1 is env0
        assert t.is_a_subtype_of_or_equal_to(T_List)
        return (t, env0)

@P("{EX} : {EX} occurrences of {code_unit_lit}")
class _:
    def s_expr(expr, env0, _):
        [ex, cu_lit] = expr.children
        env1 = env0.ensure_expr_is_of_type(ex, T_MathInteger_)
        env0.assert_expr_is_of_type(cu_lit, T_code_unit_)
        return (ListType(T_code_unit_), env1)

@P("{EXPR} : the List of {nonterminal} items in {PROD_REF}, in source text order")
class _:
    def s_expr(expr, env0, _):
        [nont, prod_ref] = expr.children
        env0.assert_expr_is_of_type(prod_ref, T_Parse_Node)
        return (ListType(T_Parse_Node), env0)

@P("{EXPR} : a List of {EX} {LITERAL} values, indexed 1 through {EX}")
class _:
    def s_expr(expr, env0, _):
        [var, literal, var2] = expr.children
        assert var.source_text() == var2.source_text()
        env0.assert_expr_is_of_type(var, T_MathInteger_)
        (lit_t, env1) = tc_expr(literal, env0); assert env1 is env0
        return (ListType(lit_t), env1)

# ------------------------------------------------------------------------------
# modify a List:

@P("{COMMAND} : Append {EX} to the end of {EX}.")
@P("{COMMAND} : Append {EX} to {EX}.")
@P("{COMMAND} : Insert {var} as the first element of {var}.")
@P("{COMMAND} : Prepend {var} to {var}.")
@P("{SMALL_COMMAND} : append {EX} to {SETTABLE}")
class _:
    def s_nv(anode, env0):
        [value_ex, list_ex] = anode.children
        return env0.ensure_A_can_be_element_of_list_B(value_ex, list_ex)

    def d_exec(command):
        [item_ex, list_var] = command.children
        v = EXEC(item_ex, E_Value)
        L = EXEC(list_var, ES_List)
        rhs = command.prod.rhs_s
        if 'Append' in rhs or 'append' in rhs:
            L.append_one(v)
        else:
            assert NYI

@P("{COMMAND} : Append {EX} and {EX} to {EX}.")
class _:
    def s_nv(command, env0):
        [itema_ex, itemb_ex, list_ex] = command.children
        env1 = env0.ensure_A_can_be_element_of_list_B(itema_ex, list_ex)
        env2 = env1.ensure_A_can_be_element_of_list_B(itemb_ex, list_ex)
        return env2

@P("{COMMAND} : Append to {var} the elements of {var}.")
class _:
    def s_nv(anode, env0):
        [lista, listb] = anode.children
        env0.assert_expr_is_of_type(lista, ListType(T_SlotName_))
        env0.assert_expr_is_of_type(listb, ListType(T_SlotName_))
        return env0

@P("{COMMAND} : Remove {var} from {var}.")
@P("{COMMAND} : Remove {var} from {DOTTING}.")
class _:
    def s_nv(anode, env0):
        [item_var, list_ex] = anode.children
        list_type = env0.assert_expr_is_of_type(list_ex, T_List)
        env0.assert_expr_is_of_type(item_var, list_type.element_type)
        return env0

@P("{COMMAND} : Remove the first element from {SETTABLE}.")
class _:
    def s_nv(anode, env0):
        [var] = anode.children
        env0.assert_expr_is_of_type(var, T_List)
        return env0

@P("{COMMAND} : Remove the first {var} elements of {SETTABLE}.")
class _:
    def s_nv(anode, env0):
        [nvar, listvar] = anode.children
        env0.assert_expr_is_of_type(nvar, T_MathNonNegativeInteger_)
        env0.assert_expr_is_of_type(listvar, T_List)
        return env0

@P("{COMMAND} : Remove the last element of {SETTABLE}.")
class _:
    def s_nv(anode, env0):
        [settable] = anode.children
        env0.assert_expr_is_of_type(settable, T_List)
        return env0

@P("{COMMAND} : Replace {var} in {var} with {var}.")
class _:
    def s_nv(anode, env0):
        [ex_var, list_var, rep_var] = anode.children
        env1 = env0.ensure_expr_is_of_type(list_var, ListType(T_PrivateElement))
        env1.assert_expr_is_of_type(ex_var, T_PrivateElement)
        env1.assert_expr_is_of_type(rep_var, T_PrivateElement)
        return env1

@P("{COMMAND} : Replace the element of {SETTABLE} whose value is {var} with an element whose value is {LITERAL}.")
class _:
    def s_nv(anode, env0):
        [list_var, elem_ex, lit] = anode.children
        env1 = env0.ensure_A_can_be_element_of_list_B(elem_ex, list_var)
        env2 = env1.ensure_A_can_be_element_of_list_B(lit, list_var)
        return env2

@P("{SMALL_COMMAND} : reverse the order of the elements of {var}")
class _:
    def s_nv(anode, env0):
        [var] = anode.children
        return env0.ensure_expr_is_of_type(var, T_List)

# ------------------------------------------------------------------------------
# iterate over a List:

@P("{EACH_THING} : element {DEFVAR} of {EX}")
@P("{EACH_THING} : element {DEFVAR} of {var}, in reverse List order")
class _:
    def s_nv(each_thing, env0):
        [loop_var, collection_expr] = each_thing.children
        (list_type, env1) = tc_expr(collection_expr, env0); assert env1 is env0
        if list_type == T_List:
            # want to assert that this doesn't happen,
            # but _kept_ in %TypedArray%.prototype.filter
            element_type = T_TBD
        else:
            assert isinstance(list_type, ListType), list_type
            element_type = list_type.element_type
        return env1.plus_new_entry(loop_var, element_type)

# ------------------------------------------------------------------------------
# whether or not the List is empty:

@P("{CONDITION_1} : {var} is now an empty List")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_List)
        return (env0, env0)

@P("{CONDITION_1} : {var} has no elements")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_List)
        return (env0, env0)

@P("{CONDITION_1} : {var} has any elements")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_List)
        return (env0, env0)

# ------------------------------------------------------------------------------
# the number of elements in the List:

@P("{CONDITION_1} : The length of {var} is {var}")
class _:
    def s_cond(cond, env0, asserting):
        [list_var, len_var] = cond.children
        env0.assert_expr_is_of_type(list_var, T_List)
        env0.assert_expr_is_of_type(len_var, T_MathNonNegativeInteger_)
        return (env0, env0)

@P("{EXPR} : the number of elements in the List {var}")
@P("{EX} : The number of elements in {var}")
@P("{EX} : the number of elements in {EX}")
@P("{NUM_COMPARAND} : the number of elements in the result of {NAMED_OPERATION_INVOCATION}")
@P("{NUM_COMPARAND} : the number of elements in {var}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_List)
        return (T_MathNonNegativeInteger_, env1)

    def d_exec(expr):
        [list_ex] = expr.children
        list_val = EXEC(list_ex, ES_List)
        return list_val.number_of_elements()

@P("{CONDITION_1} : {var} has {EX} elements")
class _:
    def s_cond(cond, env0, asserting):
        [var, ex] = cond.children
        env0.assert_expr_is_of_type(var, T_List)
        env0.assert_expr_is_of_type(ex, T_MathNonNegativeInteger_)
        return (env0, env0)

# ----------------------------
# the List contains something:

@P("{CONDITION_1} : {EX} contains any duplicate elements")
@P("{CONDITION_1} : {EX} contains any duplicate entries")
@P("{CONDITION_1} : {EX} contains no duplicate entries")
@P("{CONDITION_1} : {var} has any duplicate entries")
@P("{CONDITION_1} : {var} has no duplicate entries")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_List)
        return (env0, env0)

    def d_exec(cond):
        [container_ex] = cond.children
        L = EXEC(container_ex, ES_List)
        if 'no duplicate' in cond.prod.rhs_s:
            return not L.contains_any_duplicates()
        else:
            return L.contains_any_duplicates()

@P("{CONDITION_1} : {EX} contains a single {nonterminal}")
class _:
    def s_cond(cond, env0, asserting):
        [var, nonterminal] = cond.children
        env0.assert_expr_is_of_type(var, ListType(T_Parse_Node))
        return (env0, env0)

@P("{CONDITION_1} : {EX} contains any {nonterminal}s")
class _:
    def s_cond(cond, env0, asserting):
        [noi, nont] = cond.children
        env0.assert_expr_is_of_type(noi, ListType(T_Parse_Node))
        return (env0, env0)

    def d_exec(cond):
        [noi, nont] = cond.children
        L = EXEC(noi, ES_List)
        nt_name = nt_name_from_nonterminal_node(nont)
        return L.contains_an_element_satisfying(
            lambda e: e.symbol == nt_name
        )

@P("{CONDITION_1} : {EX} contains {VAL_DESC} {DEFVAR} such that {CONDITION_1}")
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

@P("{CONDITION_1} : {EX} contains more than one occurrence of {starred_str}")
class _:
    def s_cond(cond, env0, asserting):
        [noi, ss] = cond.children
        env1 = env0.ensure_expr_is_of_type(noi, ListType(T_String))
        return (env1, env1)

    def d_exec(cond):
        [noi, ss] = cond.children
        L = EXEC(noi, ES_List)
        v = EXEC(ss, E_Value)
        return L.number_of_occurrences_of(v) > 1

@P('{CONDITION_1} : Exactly one element of {var} meets this criterion')
class _:
    def s_cond(cond, env0, _):
        [list_var] = cond.children
        env0.ensure_expr_is_of_type(list_var, T_List)
        return (env0, env0)

# ------------------------------------------------------------------------------
# questions involving multiple Lists:

@P("{CONDITION_1} : {var} and {var} have the same number of elements")
class _:
    def s_cond(cond, env0, asserting):
        [vara, varb] = cond.children
        env0.assert_expr_is_of_type(vara, T_List)
        env0.assert_expr_is_of_type(varb, T_List)
        return (env0, env0)

@P("{CONDITION_1} : {var} and {var} do not have the same number of elements")
class _:
    def s_cond(cond, env0, asserting):
        [vara, varb] = cond.children
        env0.assert_expr_is_of_type(vara, T_List)
        env0.assert_expr_is_of_type(varb, T_List)
        return (env0, env0)

@P("{CONDITION_1} : {var}, {var}, and {var} have the same number of elements")
class _:
    def s_cond(cond, env0, asserting):
        [vara, varb, varc] = cond.children
        env0.assert_expr_is_of_type(vara, T_List)
        env0.assert_expr_is_of_type(varb, T_List)
        env0.assert_expr_is_of_type(varc, T_List)
        return (env0, env0)

@P("{CONDITION_1} : any element of {NAMED_OPERATION_INVOCATION} also occurs in {NAMED_OPERATION_INVOCATION}")
class _:
    def s_cond(cond, env0, asserting):
        [noi1, noi2] = cond.children
        env0.assert_expr_is_of_type(noi1, T_List)
        env0.assert_expr_is_of_type(noi2, T_List)
        return (env0, env0)

    def d_exec(cond):
        [noi1, noi2] = cond.children
        L1 = EXEC(noi1, ES_List)
        L2 = EXEC(noi2, ES_List)
        return L1.has_any_element_in_common_with(L2)

@P("{CONDITION_1} : any element of {NAMED_OPERATION_INVOCATION} does not also occur in either {NAMED_OPERATION_INVOCATION}, or {NAMED_OPERATION_INVOCATION}")
class _:
    def s_cond(cond, env0, asserting):
        [noia, noib, noic] = cond.children
        env0.assert_expr_is_of_type(noia, T_List)
        env0.assert_expr_is_of_type(noib, T_List)
        env0.assert_expr_is_of_type(noic, T_List)
        return (env0, env0)

    def d_exec(cond):
        [noi1, noi2, noi3] = cond.children
        L1 = EXEC(noi1, ES_List)
        L2 = EXEC(noi2, ES_List)
        L3 = EXEC(noi3, ES_List)
        return any(
            not (L2.contains(element) or L3.contains(element))
            for element in L1.elements()
        )

# ------------------------------------------------------------------------------
# identify an element in a List:

@P("{EXPR} : the first element of {SETTABLE}")
@P("{EXPR} : the last element of {var}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        list_type = env0.assert_expr_is_of_type(var, T_List)
        return (list_type.element_type, env0)

@P("{EXPR} : the sole element of {PP_NAMED_OPERATION_INVOCATION}")
@P("{EXPR} : the sole element of {var}")
class _:
    def s_expr(expr, env0, _):
        [noi] = expr.children
        list_type = env0.assert_expr_is_of_type(noi, T_List)
        return (list_type.element_type, env0)

@P("{EXPR} : {var}<sup>th</sup> element of {EX}")
class _:
    def s_expr(expr, env0, _):
        [subscript_var, list_ex] = expr.children
        env0.assert_expr_is_of_type(subscript_var, T_MathInteger_)
        list_type = env0.assert_expr_is_of_type(list_ex, T_List)
        return (list_type.element_type, env0)

# ------------------------------------------------------------------------------
# forms that are used for various kinds of container:

@P("{CONDITION_1} : {EX} is empty")
@P("{CONDITION_1} : {EX} is not empty")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        # polymorphic
        env0.assert_expr_is_of_type(var, T_CharSet | T_List | T_String)
        # XXX For String, change spec to "is [not] the empty String" ?
        return (env0, env0)

    def d_exec(cond):
        [ex] = cond.children
        L = EXEC(ex, ES_List)
        if 'is not' in cond.prod.rhs_s:
            return not L.is_empty()
        else:
            return L.is_empty()

@P("{CONDITION_1} : {var} does not include the element {LITERAL}")
class _:
    def s_cond(cond, env0, asserting):
        [list_var, item_lit] = cond.children
        env1 = env0.ensure_expr_is_of_type(list_var, ListType(T_String))
        env0.assert_expr_is_of_type(item_lit, T_String)
        return (env1, env1)

    def d_exec(cond):
        [var, lit] = cond.children
        L = EXEC(var, ES_List)
        v = EXEC(lit, E_Value)
        return not L.contains(v)

@P("{CONDITION_1} : {EX} contains {EX}")
@P("{CONDITION_1} : {EX} does not contain {EX}")
class _:
    def s_cond(cond, env0, asserting):
        [container_ex, value_var] = cond.children
        (container_type, container_env) = tc_expr(container_ex, env0)
        # polymorphic
        if container_type.is_a_subtype_of_or_equal_to(T_String):
            env1 = container_env.ensure_expr_is_of_type(value_var, T_String | T_code_unit_)
        elif container_type.is_a_subtype_of_or_equal_to(T_CharSet):
            env1 = container_env.ensure_expr_is_of_type(value_var, T_character_ | ListType(T_character_))
        elif container_type.is_a_subtype_of_or_equal_to(T_Relation):
            env1 = container_env.ensure_expr_is_of_type(value_var, T_event_pair_)
        else:
            env1 = env0.ensure_A_can_be_element_of_list_B(value_var, container_ex)
        return (env1, env1)

    def d_exec(cond):
        [container_ex, element_ex] = cond.children
        container = EXEC(container_ex, (ES_List, ES_UnicodeCodePoints))
        e = EXEC(element_ex, E_Value)
        if container.isan(ES_List):
            contains_it = container.contains(e)
        elif container.isan(ES_UnicodeCodePoints):
            if e.isan(ES_UnicodeCodePoints):
                assert e.number_of_code_points() == 1
                [e] = e.code_points()
            contains_it = container.contains_code_point(e)
        else:
            assert 0, container
        if 'does not contain' in cond.prod.rhs_s:
            return not contains_it
        else:
            return contains_it

@P("{CONDITION_1} : {var} occurs exactly once in {var}")
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

@P("{SETTABLE} : {var}[{EX}]")
@P("{SETTABLE} : {DOTTING}[{EX}]")
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
# The Record Specification Type

#> The <dfn>Record</dfn> type
#> is used to describe data aggregations
#> within the algorithms of this specification.

class ES_Record(ES_Value):
    pass

@P("{EXPR} : a new Record")
# Once, in CreateIntrinsics
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_Intrinsics_Record, env0)

# ------------------------------------------------------------------------------
#> A Record type value consists of one or more named fields.
#> The value of each field is an ECMAScript language value or specification value.
#> Field names are always enclosed in double brackets, for example [[Value]].

@P("{CONDITION_1} : {SETTABLE} has an? {DSBN} field")
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

@P("{CONDITION_1} : {var} does not have an? {DSBN} field")
class _:
    def s_cond(cond, env0, asserting):
        [var, dsbn] = cond.children
        env1 = env0.ensure_expr_is_of_type(var, T_Record)
        # XXX We should check whether its type says it *could* have such a field.
        # XXX The particular DSBN could have a (sub-)type-constraining effect
        return (env1, env1)

@P("{CONDITION_1} : That Record's {dsb_word} is {EX}")
class _:
    def s_cond(cond, env0, asserting):
        [dsb_word, ex] = cond.children
        dsbn_name = dsb_word.source_text()
        # "That Record" is from prev step's "contains a Record"
        assert dsbn_name == '[[Module]]'
        field_type = T_Module_Record
        env0.assert_expr_is_of_type(ex, field_type)
        return (env0, env0)

@P("{VAL_DESC} : a Record with fields {dsb_word} ({VALUE_DESCRIPTION}) and {dsb_word} ({VALUE_DESCRIPTION})")
@P("{VAL_DESC} : a Record with fields {dsb_word} ({VALUE_DESCRIPTION}), {dsb_word} ({VALUE_DESCRIPTION}), and {dsb_word} ({VALUE_DESCRIPTION})")
@P("{LIST_ELEMENTS_DESCRIPTION} : Records with fields {dsb_word} ({VAL_DESC}) and {dsb_word} ({VAL_DESC})")
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

@P("{SETTABLE} : the {DSBN} field of {EXPR}")
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

# ------------------------------------------------------------------------------
#> For notational convenience within this specification,
#> an object literal-like syntax can be used to express a Record value.
#> ...
#> Schema for commonly used Record field combinations may be named,
#> and that name may be used as a prefix to a literal Record value
#> to identify the specific kind of aggregations that is being described

@P("{RECORD_CONSTRUCTOR} : {RECORD_CONSTRUCTOR_PREFIX} { {FIELDS} }")
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

# ------------------------------------------------------------------------------
#> In specification text and algorithms,
#> dot notation may be used to refer to
#> a specific field of a Record value.
#> For example, if R is the record shown in the previous paragraph then
#> R.[[Field2]] is shorthand for “the field of R named [[Field2]]”.

@P("{DOTTING} : {var}.{DSBN}")
@P("{DOTTING} : {DOTTING}.{DSBN}")
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

                isom_decls = decls_for_isom_named_[dsbn_name]
                if len(isom_decls) == 0:
                    # This might be a new internal method/slot
                    # that pseudocode_semantics doesn't know about yet.
                    # Or, lhs_t might be a union-type including
                    # both an object-type and a record-type
                    # (E.g., the result of Evaluation might be an Object or a Reference Record),
                    # but the dotting is only for the record possibility.
                    part_of_dotting_t = None
                
                elif len(isom_decls) == 1:
                    [isom_decl] = isom_decls
                    assert isom_decl.name == dsbn_name
                    assert isom_decl.holder_stype, dsbn_name
                    if part_of_lhs_t.is_a_subtype_of_or_equal_to(isom_decl.holder_stype):
                        # great
                        part_of_dotting_t = isom_decl.stype
                    elif isom_decl.holder_stype.is_a_subtype_of_or_equal_to(part_of_lhs_t):
                        # E.g., `_O_.[[TypedArrayName]]` and we merely know that _O_ is an Object.
                        # But only a TypedArray has a [[TypedArrayName]] slot,
                        # so we can narrow the stype of _O_ to TypedArray,
                        # in addition to knowing the stype of the dotting.
                        msg_lines.append(f"within {part_of_lhs_t}, {isom_decl.holder_stype} supports .{dsbn_name}")
                        part_of_lhs_t = isom_decl.holder_stype
                        part_of_dotting_t = isom_decl.stype
                    else:
                        part_of_dotting_t = None

                else:
                    # The isom_decls whose holder_stype is a supertype/subtype of {part_of_lhs_t}
                    super_isom_decls = []
                    sub_isom_decls = []
                    for isom_decl in isom_decls:
                        if part_of_lhs_t.is_a_subtype_of_or_equal_to(isom_decl.holder_stype):
                            super_isom_decls.append(isom_decl)
                        elif isom_decl.holder_stype.is_a_subtype_of_or_equal_to(part_of_lhs_t):
                            sub_isom_decls.append(isom_decl)
                        else:
                            # That's fine, isom_decl is just about some unrelated object-type
                            # that happens to also have a slot/method by that name.
                            pass

                    if len(super_isom_decls) == 0:
                        # There is no isom_decl whose holder_stype
                        # is a super-type of (or equal to) {part_of_lhs_t}.

                        # But there should be one or more
                        # whose holder_stype is a sub-type of it.

                        if len(sub_isom_decls) == 0:
                            assert 0
                        else:
                            union_of_holder_stypes = union_of_types([
                                isom_decl.holder_stype
                                for isom_decl in sub_isom_decls
                            ])
                            union_of_result_stypes = union_of_types([
                                isom_decl.stype
                                for isom_decl in sub_isom_decls
                            ])
                            msg_lines.append(f"Within {part_of_lhs_t}, {union_of_holder_stypes} supports .{dsbn_name}")
                            part_of_lhs_t = union_of_holder_stypes
                            part_of_dotting_t = union_of_result_stypes
                    else:
                        # There's at least one isom_decl whose holder_stype
                        # is a super-type of {part_of_lhs_t}.

                        # In practice, it would be odd
                        # (probably a mistake in some call to declare_isom)
                        # for there to be *more* than one.
                        assert len(super_isom_decls) == 1

                        # Similarly, it would be odd
                        # for there to be any isom_decls
                        # whose holder_stype is a subtype of {part_of_lhs_t}.
                        assert len(sub_isom_decls) == 0

                        [isom_decl] = super_isom_decls
                        part_of_dotting_t = isom_decl.stype

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

# for 10.2.4 AddRestrictedFunctionProperties
@P("{CONDITION_1} : {DOTTING} exists and has been initialized")
class _:
    def s_cond(cond, env0, asserting):
        [dotting] = cond.children
        return (env0, env0)

@P("{CONDITION_1} : {var} does not have any fields")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_Property_Descriptor)
        return (env0, env0)

# ------------------------------------------------------------------------------
# List of Records

@P("{CONDITION_1} : All elements of {var} have their {dsb_word} field set to {LITERAL}, {dsb_word} field set to {LITERAL}, and {dsb_word} field set to {LITERAL}")
class _:
    def s_cond(cond, env0, asserting):
        [var, dsb1, lit1, dsb2, lit2, dsb3, lit3] = cond.children
        assert dsb1.source_text() == '[[AsyncEvaluation]]'
        assert dsb2.source_text() == '[[PendingAsyncDependencies]]'
        assert dsb3.source_text() == '[[EvaluationError]]'
        # could check that the lits have the right type.
        env0.assert_expr_is_of_type(var, ListType(T_Cyclic_Module_Record))
        return (env0, env0)

@P("{CONDITION_1} : {EX} contains a Record {DEFVAR} such that {CONDITION_1}")
class _:
    def s_cond(cond, env0, asserting):
        [ex, var, stcond] = cond.children
        (ex_t, env1) = tc_expr(ex, env0); assert env1 is env0
        assert ex_t.is_a_subtype_of_or_equal_to(T_List)
        assert ex_t.element_type.is_a_subtype_of_or_equal_to(T_Record)
        env_for_cond = env0.plus_new_entry(var, ex_t.element_type)
        (cond_t_env, cond_f_env) = tc_cond(stcond, env_for_cond)
        return (cond_t_env, env0)

@P("{CONDITION_1} : {EX} contains a Record whose {dsb_word} is {var}")
@P("{CONDITION_1} : Exactly one element of {DOTTING} is a Record whose {dsb_word} is {var}")
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

@P("{EXPR} : the element of {EX} whose {DSBN} is {EX}")
@P("{EXPR} : the element of {EX} whose {DSBN} field is {var}")
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

@P("{EXPR} : the Record in {DOTTING} whose {dsb_word} is {var}")
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

# ------------------------------------------------------------------------------

def s_X_and_Y_are_the_same_Foo_Record(cond, record_type, env0):
    [x, y] = cond.children

    (x_t, env1) = tc_expr(x, env0); env1 is env0
    (y_t, env1) = tc_expr(y, env0); env1 is env0

    check_comparison(cond, 'are the same X Record', x_t, y_t)

    # In the env where they are the same Foo Record,
    # they must necessarily both be Foo Records.
    # In the env where they're not the same Foo Record,
    # there's no constraint on what they are.

    (x_in, _) = x_t.split_by(record_type)
    (y_in, _) = y_t.split_by(record_type)

    env_same = (
        env0
        .with_expr_type_narrowed(x, x_in)
        .with_expr_type_narrowed(y, y_in)
    )

    if 'are the same' in cond.prod.rhs_s:
        return (env_same, env0)
    elif 'are not the same' in cond.prod.rhs_s:
        return (env0, env_same)
    else:
        assert 0

# ==============================================================================
#@ 6.2.3 The Set and Relation Specification Types

#> Values of the Relation type
#> are Sets of ordered pairs of values from its value domain.

@P("{EXPR} : an empty Set")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_Set, env0)

@P("{PAIR} : ({EX}, {EX})")
class _:
    def s_expr(expr, env0, _):
        [a, b] = expr.children
        # over-specific:
        env0.assert_expr_is_of_type(a, T_Event)
        env0.assert_expr_is_of_type(b, T_Event)
        return (T_event_pair_, env0)

@P("{COMMAND} : Add {var} to {var}.")
@P("{SMALL_COMMAND} : add {var} to {var}")
class _:
    def s_nv(anode, env0):
        [item_var, collection_var] = anode.children
        (item_type, env1) = tc_expr(item_var, env0); assert env1 is env0
        (collection_type, env2) = tc_expr(collection_var, env0); assert env2 is env0
        if item_type.is_a_subtype_of_or_equal_to(T_Event) and collection_type == T_Set:
            pass
        elif item_type.is_a_subtype_of_or_equal_to(ListType(T_character_)) and collection_type == T_CharSet:
            pass
        else:
            assert 0
        return env0

@P("{CONDITION_1} : the pairs {PAIR} and {PAIR} are in {EX}")
@P("{CONDITION_1} : the pairs {PAIR} and {PAIR} are not in {EX}")
class _:
    def s_cond(cond, env0, asserting):
        [paira, pairb, ex] = cond.children
        env0.assert_expr_is_of_type(paira, T_event_pair_)
        env0.assert_expr_is_of_type(pairb, T_event_pair_)
        env0.assert_expr_is_of_type(ex, T_Relation)
        return (env0, env0)

@P("{CONDITION_1} : {EX} contains either {PAIR} or {PAIR}")
class _:
    def s_cond(cond, env0, asserting):
        [ex, paira, pairb] = cond.children
        env0.assert_expr_is_of_type(paira, T_event_pair_)
        env0.assert_expr_is_of_type(pairb, T_event_pair_)
        env0.assert_expr_is_of_type(ex, T_Relation)
        return (env0, env0)

@P("{CONDITION_1} : {var} is not in {PREFIX_PAREN}")
class _:
    def s_cond(cond, env0, asserting):
        [item_var, set_pp] = cond.children
        env0.assert_expr_is_of_type(set_pp, T_Set)
        env0.assert_expr_is_of_type(item_var, T_Event)
        return (env0, env0)

# ==============================================================================
#@ 6.2.4 The Completion Record Specification Type

#> The <dfn>Completion Record</dfn> specification type
#> is used to explain the runtime propagation of values and control flow ...

class ES_CompletionRecord(ES_Record):
    pass

@P("{VAL_DESC} : a Completion Record")
class _:
    s_tb = T_Completion_Record

@P("{VAL_DESC} : any value except a Completion Record")
class _:
    s_tb = T_Tangible_ | T_Intangible_

@P("{EXPR} : a new implementation-defined Completion Record")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_Completion_Record, env0)

@P('{CONDITION_1} : {SETTABLE} and {SETTABLE} are the same Completion Record')
class _:
    def s_cond(cond, env0, asserting):
        return s_X_and_Y_are_the_same_Foo_Record(cond, T_Completion_Record, env0)

#> The following shorthand terms are sometimes used to refer to Completion Records.

#-------------------------------------------------------------------------------
#> <dfn>normal completion</dfn> refers to any Completion Record with a [[Type]] value of ~normal~.

def NormalCompletionType(value_type):
    return RecordType(
        'Completion Record',
        (
            ('[[Type]]',  T_tilde_normal_),
            ('[[Value]]', value_type),
        )
    )

@P("{VAL_DESC} : a normal completion")
class _:
    s_tb = T_normal_completion

# ------------------------------------------------------------------------------
#> a <dfn>normal completion containing</dfn> some type of value
#> refers to a normal completion
#> that has a value of that type in its [[Value]] field.

@P("{VAL_DESC} : a normal completion containing {VALUE_DESCRIPTION}")
class _:
    def s_tb(vd, env):
        [child] = vd.children
        (sub_t, sup_t) = type_bracket_for(child, env)
        return (NormalCompletionType(sub_t), NormalCompletionType(sup_t))

@P("{CONDITION_1} : {var} is a normal completion with a value of {LITERAL}. The possible sources of this value are Await or, if the async function doesn't await anything, step {h_emu_xref} above")
class _:
    def s_cond(cond, env0, asserting):
        [var, literal, _] = cond.children
        env0.assert_expr_is_of_type(literal, T_tilde_unused_)
        return env0.with_type_test(var, 'is a', NormalCompletionType(T_tilde_unused_), asserting)

#-------------------------------------------------------------------------------
#> <dfn>break completion</dfn> refers to any Completion Record with a [[Type]] value of ~break~.

@P("{VAL_DESC} : a break completion")
class _:
    s_tb = T_break_completion

#-------------------------------------------------------------------------------
#> <dfn>continue completion</dfn> refers to any Completion Record with a [[Type]] value of ~continue~.

@P("{VAL_DESC} : a continue completion")
class _:
    s_tb = T_continue_completion

#-------------------------------------------------------------------------------
#> <dfn>return completion</dfn> refers to any Completion Record with a [[Type]] value of ~return~.

@P("{VAL_DESC} : a return completion")
class _:
    s_tb = T_return_completion

#-------------------------------------------------------------------------------
#> <dfn>throw completion</dfn> refers to any Completion Record with a [[Type]] value of ~throw~.

def ThrowCompletionType(error_type):
    return RecordType(
        'Completion Record',
        (
            ('[[Type]]', T_tilde_throw_),
            ('[[Value]]', error_type),
        )
    )

@P("{VAL_DESC} : a throw completion")
class _:
    s_tb = T_throw_completion

#-------------------------------------------------------------------------------
#> <dfn>abrupt completion</dfn> refers to any Completion Record with a [[Type]] value other than ~normal~.

@P("{VAL_DESC} : an abrupt completion")
class _:
    s_tb = T_abrupt_completion

@P("{CONDITION_1} : The next step never returns an abrupt completion because {CONDITION_1}")
class _:
    def s_cond(cond, env0, asserting):
        [subcond] = cond.children
        return tc_cond(subcond, env0, asserting)

# ==============================================================================
#@ 6.2.5 The Reference Record Specification Type

@P("{VAL_DESC} : a Reference Record")
class _:
    s_tb = T_Reference_Record

@P("{VAL_DESC} : a Super Reference Record")
class _:
    s_tb = a_subset_of(T_Reference_Record)

# ==============================================================================
#@ 6.2.6 The Property Descriptor Specification Type

@P("{VAL_DESC} : a Property Descriptor")
class _:
    s_tb = T_Property_Descriptor

@P("{VAL_DESC} : a fully populated Property Descriptor")
class _:
    s_tb = a_subset_of(T_Property_Descriptor)

@P("{EXPR} : a newly created Property Descriptor with no fields")
@P("{EXPR} : a new Property Descriptor that initially has no fields")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_Property_Descriptor, env0)

# for 9.3.4 SetDefaultGlobalBindings
@P("{EXPR} : the fully populated data Property Descriptor for the property, containing the specified attributes for the property. For properties listed in {h_emu_xref}, {h_emu_xref}, or {h_emu_xref} the value of the {DSBN} attribute is the corresponding intrinsic object from {var}")
class _:
    def s_expr(expr, env0, _):
        [emu_xref1, emu_xref2, emu_xref3, dsbn, var] = expr.children
        env0.assert_expr_is_of_type(var, T_Realm_Record)
        return (T_Property_Descriptor, env0)

@P("{CONDITION_1} : {var} has attribute values { {DSBN}: *true*, {DSBN}: *true* }")
class _:
    def s_cond(cond, env0, asserting):
        [var, dsbn1, dsbn2] = cond.children
        env1 = env0.ensure_expr_is_of_type(var, T_Property_Descriptor)
        assert dsbn1.source_text() == '[[Writable]]'
        assert dsbn2.source_text() == '[[Enumerable]]'
        return (env1, env1)

@P("{COMMAND} : Replace the property named {var} of object {var} with an? {PROPERTY_KIND} property whose {dsb_word} and {dsb_word} attributes are set to {var} and {var}, respectively, and whose {dsb_word} and {dsb_word} attributes are set to the value of the corresponding field in {var} if {var} has that field, or to the attribute's {h_emu_xref} otherwise.")
class _:
    def s_nv(anode, env0):
        [name_var, obj_var, kind, dsbw1, dsbw2, field_var1, field_var2, dsbw3, dsbw4, desc_var, desc_var2, emu_xref] = anode.children
        assert desc_var.source_text() == desc_var2.source_text()
        env0.ensure_expr_is_of_type(name_var, T_String | T_Symbol)
        env0.assert_expr_is_of_type(obj_var, T_Object)
        env0.assert_expr_is_of_type(desc_var, T_Property_Descriptor)
        return env0

@P("{EACH_THING} : field of {var}")
class _:
    def s_nv(each_thing, env0):
        [desc_var] = each_thing.children
        loop_var = None # todo: no loop variable!
        env0.assert_expr_is_of_type(desc_var, T_Property_Descriptor)
        return env0

@P("{SMALL_COMMAND} : set the corresponding attribute of the property named {var} of object {var} to the value of the field")
class _:
    def s_nv(anode, env0):
        [name_var, obj_var] = anode.children
        env0.ensure_expr_is_of_type(name_var, T_String | T_Symbol)
        env0.assert_expr_is_of_type(obj_var, T_Object)
        return env0

# ==============================================================================
#@ 6.2.7 The Environment Record Specification Type

# (See 9.1 Environment Records)

# ==============================================================================
#@ 6.2.8 The Abstract Closure Specification Type

@P("{VAL_DESC} : an Abstract Closure")
class _:
    s_tb = T_proc_

@P("{VAL_DESC} : an Abstract Closure with no parameters")
class _:
    s_tb = ProcType((), T_Completion_Record)

@P("{VAL_DESC} : an Abstract Closure with two parameters")
class _:
    s_tb = ProcType((T_Tangible_, T_Tangible_), NormalCompletionType(T_Number) | T_throw_completion)

@P("{MULTILINE_EXPR} : a new {CLOSURE_KIND} with {CLOSURE_PARAMETERS} that captures {CLOSURE_CAPTURES} and performs the following {CLOSURE_STEPS} when called:{IND_COMMANDS}")
class _:
    def s_expr(expr, env0, _):
        [clo_kind, clo_parameters, clo_captures, _, commands] = expr.children
        clo_kind = clo_kind.source_text()

        # -----

        env_for_commands = Env(env0)
        env_for_commands.alg_species = 'op: closure'

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

        class AbstractClosureAlgDefn: pass
        alg_defn = AbstractClosureAlgDefn()
        alg_defn.parent_header = None
        alg_defn.anodes = [commands]

        defns = [alg_defn]
        env_after_commands = tc_proc(None, defns, env_for_commands)
        t = ProcType(tuple(clo_param_types), env_after_commands.vars['*return*'])
        return (t, env0)

# ==============================================================================
#@ 6.2.9 Data Blocks

@P("{VAL_DESC} : a Data Block")
class _:
    s_tb = T_Data_Block

@P("{VAL_DESC} : a Shared Data Block")
class _:
    s_tb = T_Shared_Data_Block

@P("{EXPR} : a new Data Block value consisting of {var} bytes. If it is impossible to create such a Data Block, throw a {ERROR_TYPE} exception")
class _:
    def s_expr(expr, env0, _):
        [var, error_type] = expr.children
        (t, env1) = tc_expr(var, env0)
        assert env1 is env0
        assert t.is_a_subtype_of_or_equal_to(T_MathInteger_)
        proc_add_return(env0, ThrowCompletionType(type_for_ERROR_TYPE(error_type)), error_type)
        return (T_Data_Block, env1)

@P("{EXPR} : a new Shared Data Block value consisting of {var} bytes. If it is impossible to create such a Shared Data Block, throw a {ERROR_TYPE} exception")
class _:
    def s_expr(expr, env0, _):
        [var, error_type] = expr.children
        (t, env1) = tc_expr(var, env0)
        assert env1 is env0
        assert t.is_a_subtype_of_or_equal_to(T_MathInteger_)
        proc_add_return(env0, ThrowCompletionType(type_for_ERROR_TYPE(error_type)), error_type)
        return (T_Shared_Data_Block, env1)

@P("{CONDITION_1} : it is impossible to create a new Shared Data Block value consisting of {var} bytes")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_MathNonNegativeInteger_)
        return (env0, env0)

@P("{CONDITION_1} : it is not possible to create a Data Block {var} consisting of {var} bytes")
class _:
    def s_cond(cond, env0, asserting):
        [db_var, nbytes_var] = cond.children
        env0.assert_expr_is_of_type(db_var, T_Data_Block)
        env1 = env0.ensure_expr_is_of_type(nbytes_var, T_MathNonNegativeInteger_)
        return (env1, env1)

@P("{COMMAND} : Set all of the bytes of {var} to 0.")
class _:
    def s_nv(anode, env0):
        [var] = anode.children
        env1 = env0.ensure_expr_is_of_type(var, T_Data_Block)
        return env1

@P("{COMMAND} : Store the individual bytes of {var} into {var}, starting at {var}[{var}].")
class _:
    def s_nv(anode, env0):
        [var1, var2, var3, var4] = anode.children
        env0.assert_expr_is_of_type(var1, ListType(T_MathInteger_))
        env1 = env0.ensure_expr_is_of_type(var2, T_Data_Block)
        assert var3.children == var2.children
        env0.assert_expr_is_of_type(var4, T_MathInteger_)
        return env1

@P("{EXPR} : the number of bytes in {var}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_Data_Block | T_Shared_Data_Block)
        return (T_MathNonNegativeInteger_, env1)

@P("{EXPR} : a List of length {var} whose elements are the sequence of {var} bytes starting with {var}[{var}]")
class _:
    def s_expr(expr, env0, _):
        [var1, var2, var3, var4] = expr.children
        assert var1.children == var2.children
        env0.assert_expr_is_of_type(var1, T_MathInteger_)
        env1 = env0.ensure_expr_is_of_type(var3, T_Data_Block | T_Shared_Data_Block)
        env0.assert_expr_is_of_type(var4, T_MathInteger_)
        return (ListType(T_MathInteger_), env1)

@P("{EXPR} : a List whose elements are bytes from {var} at indices in {INTERVAL}")
class _:
    def s_expr(expr, env0, _):
        [data_var, interval] = expr.children
        env1 = env0.ensure_expr_is_of_type(data_var, T_Data_Block | T_Shared_Data_Block)
        env1.assert_expr_is_of_type(interval, T_MathNonNegativeInteger_)
        return (ListType(T_MathNonNegativeInteger_), env1)

@P("{EACH_THING} : index {DEFVAR} of {var}")
class _:
    def s_nv(each_thing, env0):
        [loop_var, collection_var] = each_thing.children
        env0.assert_expr_is_of_type(collection_var, T_Shared_Data_Block)
        return env0.plus_new_entry(loop_var, T_MathInteger_)

@P("{CONDITION_1} : {EX} and {EX} are valid byte offsets within the memory of {var}")
class _:
    def s_cond(cond, env0, asserting):
        [offset1, offset2, sdb] = cond.children
        env1 = env0.ensure_expr_is_of_type(offset1, T_MathInteger_)
        env1.assert_expr_is_of_type(offset2, T_MathInteger_)
        env1.assert_expr_is_of_type(sdb, T_Shared_Data_Block)
        return (env1, env1)

# ==============================================================================
#@ 6.2.10 The PrivateElement Specification Type

@P("{VAL_DESC} : a PrivateElement")
@P("{LIST_ELEMENTS_DESCRIPTION} : PrivateElements")
class _:
    s_tb = T_PrivateElement

# ==============================================================================
#@ 6.2.11 The ClassFieldDefinition Record Specification Type

@P("{VAL_DESC} : a ClassFieldDefinition Record")
@P("{LIST_ELEMENTS_DESCRIPTION} : ClassFieldDefinition Records")
class _:
    s_tb = T_ClassFieldDefinition_Record

# ==============================================================================
#@ 6.2.12 Private Names

@P("{VAL_DESC} : a Private Name")
@P("{LIST_ELEMENTS_DESCRIPTION} : Private Names")
class _:
    s_tb = T_Private_Name

@P("{VAL_DESC} : a property key or Private Name")
# SPEC BUG: should be "or *a* Private Name"
class _:
    s_tb = T_String | T_Symbol | T_Private_Name

@P("{CONDITION_1} : {EX} contains a Private Name whose {dsb_word} is {var}")
class _:
    def s_cond(cond, env0, asserting):
        [ex, dsb_word, var] = cond.children
        env0.assert_expr_is_of_type(ex, ListType(T_Private_Name))
        assert dsb_word.source_text() == '[[Description]]'
        env0.assert_expr_is_of_type(var, T_String)
        return (env0, env0)

@P("{CONDITION_1} : Exactly one element of {var} is a Private Name whose {dsb_word} is {var}")
class _:
    def s_cond(cond, env0, asserting):
        [list_var, dsb_word, var] = cond.children
        env0.assert_expr_is_of_type(list_var, ListType(T_Private_Name))
        assert dsb_word.source_text() == '[[Description]]'
        env0.assert_expr_is_of_type(var, T_String)
        return (env0, env0)

@P("{EXPR} : a new Private Name whose {dsb_word} is {var}")
class _:
    def s_expr(expr, env0, _):
        [dsb_word, var] = expr.children
        assert dsb_word.source_text() == '[[Description]]'
        env0.assert_expr_is_of_type(var, T_String)
        return (T_Private_Name, env0)

@P("{EXPR} : the Private Name in {var} whose {dsb_word} is {var}")
class _:
    def s_expr(expr, env0, _):
        [list_var, dsb_word, var] = expr.children
        env0.assert_expr_is_of_type(list_var, ListType(T_Private_Name))
        assert dsb_word.source_text() == '[[Description]]'
        env0.assert_expr_is_of_type(var, T_String)
        return (T_Private_Name, env0)

# ==============================================================================
#@ 6.2.13 The ClassStaticBlockDefinition Record Specification Type

@P("{VAL_DESC} : a ClassStaticBlockDefinition Record")
class _:
    s_tb = T_ClassStaticBlockDefinition_Record

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 7 Abstract Operations

# ==============================================================================
#@ 7.1.13 ToBigInt

@P("{EXPR} : the value that {var} corresponds to in {h_emu_xref}")
class _:
    def s_expr(expr, env0, _):
        [var, xref] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_Primitive)
        assert xref.source_text() == '<emu-xref href="#table-tobigint"></emu-xref>'
        return (T_BigInt | ThrowCompletionType(T_TypeError) | ThrowCompletionType(T_SyntaxError), env1)

# ==============================================================================
#@ 7.3.1 MakeBasicObject

@P("{CONDITION_1} : the caller will not be overriding both {var}'s {DSBN} and {DSBN} essential internal methods")
@P("{CONDITION_1} : the caller will not be overriding all of {var}'s {DSBN}, {DSBN}, and {DSBN} essential internal methods")
class _:
    def s_cond(cond, env0, asserting):
        var = cond.children[0]
        env0.assert_expr_is_of_type(var, T_Object)
        return (env0, env0)

# ==============================================================================
#@ 7.4.1 Iterator Records

#> An <dfn>Iterator Record</dfn> is a Record value
#> used to encapsulate an Iterator or AsyncIterator along with the `next` method.

@P("{VAL_DESC} : an Iterator Record")
class _:
    s_tb = T_Iterator_Record

# ==============================================================================
#@ 7.4.10 IfAbruptCloseIterator

@P("{COMMAND} : IfAbruptCloseIterator({var}, {var}).")
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

@P("{CONDITION_1} : {LOCAL_REF} Contains {G_SYM}")
# SPEC BUG: should say "is *true*"
class _:
    def s_cond(cond, env0, asserting):
        [local_ref, g_sym] = cond.children
        env0.assert_expr_is_of_type(local_ref, T_Parse_Node)
        return (env0, env0)

    def d_exec(cond):
        [local_ref, g_sym] = cond.children
        boolean_value = execute_sdo_invocation('Contains', local_ref, [g_sym])
        assert boolean_value.isan(EL_Boolean)
        return boolean_value.b

@P("{NAMED_OPERATION_INVOCATION} : {LOCAL_REF} Contains {var}")
@P("{NAMED_OPERATION_INVOCATION} : {LOCAL_REF} Contains {G_SYM}")
class _:
    def s_expr(expr, env0, _):
        [lhs, rhs] = expr.children
        return tc_sdo_invocation('Contains', lhs, [rhs], expr, env0)

    def d_exec(expr):
        [local_ref, sym] = expr.children
        return execute_sdo_invocation('Contains', local_ref, [sym])

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 9 Executable Code and Execution Contexts

# ==============================================================================
#@ 9.1 Environment Records

#> <dfn>Environment Record</dfn> is a specification type
#> used to define the association of |Identifier|s to specific variables and functions,
#> based upon the lexical nesting structure of ECMAScript code.
#> Usually an Environment Record is associated with
#> some specific syntactic structure of ECMAScript code
#> such as a |FunctionDeclaration|, a |BlockStatement|, or a |Catch| clause of a |TryStatement|.
#> Each time such code is evaluated, a new Environment Record is created
#> to record the identifier bindings that are created by that code.

def type_for_environment_record_kind(kind):
    return HierType(kind.source_text() + ' Environment Record')

@P("{VAL_DESC} : an Environment Record")
class _:
    s_tb = T_Environment_Record

@P("{VAL_DESC} : an? {ENVIRONMENT_RECORD_KIND} Environment Record")
class _:
    def s_tb(val_desc, env):
        [kind] = val_desc.children
        return type_for_environment_record_kind(kind)

@P("{EXPR} : a new {ENVIRONMENT_RECORD_KIND} Environment Record")
@P("{EXPR} : a new {ENVIRONMENT_RECORD_KIND} Environment Record containing no bindings")
class _:
    def s_expr(expr, env0, _):
        [kind] = expr.children
        t = type_for_environment_record_kind(kind)
        return (t, env0)

@P('{CONDITION_1} : {SETTABLE} and {SETTABLE} are not the same Environment Record')
@P('{CONDITION_1} : {SETTABLE} and {SETTABLE} are the same Environment Record')
class _:
    def s_cond(cond, env0, asserting):
        return s_X_and_Y_are_the_same_Foo_Record(cond, T_Environment_Record, env0)

# ==============================================================================
#@ 9.1.1.1 Declarative Environment Records

@P("{COMMAND} : Create a mutable binding in {var} for {var} and record that it is uninitialized. If {var} is *true*, record that the newly created binding may be deleted by a subsequent DeleteBinding call.")
@P("{COMMAND} : Create an immutable binding in {var} for {var} and record that it is uninitialized. If {var} is *true*, record that the newly created binding is a strict binding.")
class _:
    def s_nv(anode, env0):
        [er_var, n_var, s_var] = anode.children
        env0.assert_expr_is_of_type(er_var, T_Environment_Record)
        env0.assert_expr_is_of_type(n_var, T_String)
        env0.assert_expr_is_of_type(s_var, T_Boolean)
        return env0

@P("{COMMAND} : {h_emu_not_ref_Record} that the binding for {var} in {var} has been initialized.")
class _:
    def s_nv(anode, env0):
        [_, key_var, oer_var] = anode.children
        env0.assert_expr_is_of_type(key_var, T_String)
        env0.assert_expr_is_of_type(oer_var, T_Environment_Record)
        return env0

@P("{COMMAND} : Remove the binding for {var} from {var}.")
class _:
    def s_nv(anode, env0):
        [n_var, er_var] = anode.children
        env0.assert_expr_is_of_type(n_var, T_String)
        env0.assert_expr_is_of_type(er_var, T_Environment_Record)
        return env0

# ------------------------------------------------------------------------------

@P("{CONDITION_1} : {var} does not already have a binding for {var}")
@P("{CONDITION_1} : {var} does not have a binding for {var}")
@P("{CONDITION_1} : {var} has a binding for {var}")
@P("{CONDITION_1} : {var} must have an uninitialized binding for {var}")
class _:
    def s_cond(cond, env0, asserting):
        [er_var, n_var] = cond.children
        env0.assert_expr_is_of_type(er_var, T_Environment_Record)
        env0.assert_expr_is_of_type(n_var, T_String)
        return (env0, env0)

@P("{CONDITION_1} : the binding for {var} in {var} cannot be deleted")
@P("{CONDITION_1} : the binding for {var} in {var} is a mutable binding")
@P("{CONDITION_1} : the binding for {var} in {var} is a strict binding")
@P("{CONDITION_1} : the binding for {var} in {var} is an uninitialized binding")
@P("{CONDITION_1} : the binding for {var} in {var} has not yet been initialized")
class _:
    def s_cond(cond, env0, asserting):
        [n_var, er_var] = cond.children
        env0.assert_expr_is_of_type(n_var, T_String)
        env0.assert_expr_is_of_type(er_var, T_Environment_Record)
        return (env0, env0)

@P("{EXPR} : the value currently bound to {var} in {var}")
@P("{SETTABLE} : the bound value for {var} in {var}")
class _:
    def s_expr(expr, env0, _):
        [n_var, er_var] = expr.children
        env0.assert_expr_is_of_type(n_var, T_String)
        env0.assert_expr_is_of_type(er_var, T_Environment_Record)
        return (T_Tangible_, env0)

# for 9.1.1.1.5 SetMutableBinding
@P("{COMMAND} : Change its bound value to {var}.")
class _:
    def s_nv(anode, env0):
        # elliptical
        [var] = anode.children
        env0.assert_expr_is_of_type(var, T_Tangible_)
        return env0

# for 9.1.1.1.5 SetMutableBinding
@P("{CONDITION_1} : This is an attempt to change the value of an immutable binding")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

# ==============================================================================
#@ 9.1.1.4 Global Environment Records

@P("{CONDITION_1} : the binding exists")
class _:
    def s_cond(cond, env0, asserting):
        # elliptical
        [] = cond.children
        return (env0, env0)

@P("{CONDITION_1} : it must be in the Object Environment Record")
class _:
    def s_cond(cond, env0, asserting):
        # elliptical
        [] = cond.children
        return (env0, env0)

# ==============================================================================
#@ 9.1.1.5 Module Environment Records

@P("{CONDITION_1} : the binding for {var} is an indirect binding")
class _:
    def s_cond(cond, env0, asserting):
        # todo: make ER explicit in spec?
        [n_var] = cond.children
        env0.assert_expr_is_of_type(n_var, T_String)
        return (env0, env0)

# ==============================================================================
#@ 9.1.1.5.5 CreateImportBinding

@P("{CONDITION_1} : When {SETTABLE} is instantiated, it will have a direct binding for {var}")
# This Assert is making a statement about the future,
# so should almost certainly be a NOTE.
class _:
    def s_cond(cond, env0, asserting):
        [settable, var] = cond.children
        env0.assert_expr_is_of_type(settable, T_Environment_Record | T_tilde_empty_)
        env0.assert_expr_is_of_type(var, T_String)
        return (env0, env0)

@P("{COMMAND} : Create an immutable indirect binding in {var} for {var} that references {var} and {var} as its target binding and record that the binding is initialized.")
class _:
    def s_nv(anode, env0):
        [er_var, n_var, m_var, n2_var] = anode.children
        env0.assert_expr_is_of_type(er_var, T_Environment_Record)
        env0.assert_expr_is_of_type(n_var, T_String)
        env0.assert_expr_is_of_type(m_var, T_Module_Record)
        env0.assert_expr_is_of_type(n2_var, T_String)
        return env0

# ==============================================================================
#@ 9.2 PrivateEnvironment Records

@P("{VAL_DESC} : a PrivateEnvironment Record")
class _:
    s_tb = T_PrivateEnvironment_Record

# ==============================================================================
#@ 9.3 Realms

@P("{VAL_DESC} : a Realm Record")
class _:
    s_tb = T_Realm_Record

@P("{EXPR} : a new Realm Record")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_Realm_Record, env0)

@P("{CONDITION_1} : {SETTABLE} and {SETTABLE} are not the same Realm Record")
class _:
    def s_cond(cond, env0, asserting):
        return s_X_and_Y_are_the_same_Foo_Record(cond, T_Realm_Record, env0)

@P("{VAL_DESC} : a Record whose field names are intrinsic keys and whose values are objects")
class _:
    s_tb = T_Intrinsics_Record

# ==============================================================================
#@ 9.3.2 CreateIntrinsics

#> Set fields of _intrinsics_ with the values listed in
#> <emu-xref href="#table-well-known-intrinsic-objects"></emu-xref>.
#> The field names are the names listed in column one of the table.
#> The value of each field is a new object value
#> fully and recursively populated with property values
#> as defined by the specification of each object
#> in clauses <emu-xref href="#sec-global-object"></emu-xref>
#> through <emu-xref href="#sec-reflection"></emu-xref>.

@P("{COMMAND} : Set fields of {DOTTING} with the values listed in {h_emu_xref}. {the_field_names_are_the_names_listed_etc}")
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

#> An execution context contains whatever implementation specific state is necessary
#> to track the execution progress of its associated code.
#> Each execution context has at least the state components listed in
#> <emu-xref href="#table-state-components-for-all-execution-contexts"></emu-xref>.

@P("{VAL_DESC} : an execution context")
class _:
    s_tb = T_execution_context

@P("{VAL_DESC} : an ECMAScript code execution context")
class _:
    s_tb = T_execution_context

@P("{EXPR} : a new execution context")
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

@P("{EXPR} : the running execution context")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_execution_context, env0)

@P("{CONDITION_1} : {var} is now the running execution context")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_execution_context)
        return (env0, env0)

@P("{CONDITION_1} : {var} is the running execution context again")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_execution_context)
        return (env0, env0)

# ------------------------------------------------------------------------------
#> Each execution context has at least the state components listed in
#> <emu-xref href="#table-state-components-for-all-execution-contexts"></emu-xref>.

@P("{SETTABLE} : the {EXECUTION_CONTEXT_COMPONENT} component of {var}")
@P("{SETTABLE} : The {EXECUTION_CONTEXT_COMPONENT} of {var}")
@P("{SETTABLE} : the {EXECUTION_CONTEXT_COMPONENT} of {var}")
@P("{SETTABLE} : {var}'s {EXECUTION_CONTEXT_COMPONENT}")
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
            'Generator' : T_Generator_object_ | T_AsyncGenerator_object_,
        }[component_name]

        return (result_type, env2)

@P("{SETTABLE} : the running execution context's {EXECUTION_CONTEXT_COMPONENT}")
@P("{SETTABLE} : the {EXECUTION_CONTEXT_COMPONENT} of the running execution context")
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

# 10.3.1
@P("{COMMAND} : Perform any necessary implementation-defined initialization of {var}.")
class _:
    def s_nv(anode, env0):
        [var] = anode.children
        env0.assert_expr_is_of_type(var, T_execution_context)
        return env0

@P("{COMMAND} : Set {SETTABLE} such that when evaluation is resumed for that execution context, {var} will be called with no arguments.")
class _:
    def s_nv(anode, env0):
        [settable, var] = anode.children
        env0.assert_expr_is_of_type(settable, T_host_defined_)
        env0.assert_expr_is_of_type(var, ProcType((), T_Top_))
        return env0

# ------------------------------------------------------------------------------
#> The <dfn>execution context stack</dfn> is used to track execution contexts.

@P("{CONDITION_1} : the execution context stack is empty")
@P("{CONDITION_1} : The execution context stack is not empty")
@P("{CONDITION_1} : The execution context stack has at least two elements")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

# for 9.4.1 GetActiveScriptOrModule
@P("{EXPR} : the topmost execution context on the execution context stack whose ScriptOrModule component is not {LITERAL}")
class _:
    def s_expr(expr, env0, _):
        [literal] = expr.children
        return (T_execution_context, env0)

# for 9.4.1 GetActiveScriptOrModule
@P("{CONDITION_1} : no such execution context exists")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

@P("{EXPR} : the second to top element of the execution context stack")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_execution_context, env0)

# ------------------------------------------------------------------------------
#> The running execution context is always the top element of this stack.

# ------------------------------------------------------------------------------
#> A new execution context is created
#> whenever control is transferred
#> from the executable code associated with the currently running execution context
#> to executable code that is not associated with that execution context.
#> The newly created execution context is pushed onto the stack
#> and becomes the running execution context.

@P("{COMMAND} : Push {var} onto the execution context stack; {var} is now the running execution context.")
class _:
    def s_nv(anode, env0):
        [var1, var2] = anode.children
        assert var1.children == var2.children
        env1 = env0.ensure_expr_is_of_type(var1, T_execution_context)
        return env1

@P("{COMMAND} : Remove {var} from the execution context stack.")
class _:
    def s_nv(anode, env0):
        [avar] = anode.children
        env0.assert_expr_is_of_type(avar, T_execution_context)
        return env0

@P("{COMMAND} : Remove {var} from the execution context stack and restore the execution context that is at the top of the execution context stack as the running execution context.")
class _:
    def s_nv(anode, env0):
        [var] = anode.children
        env0.assert_expr_is_of_type(var, T_execution_context)
        return env0

@P("{COMMAND} : Remove {var} from the execution context stack and restore {var} as the running execution context.")
class _:
    def s_nv(anode, env0):
        [avar, bvar] = anode.children
        env0.assert_expr_is_of_type(avar, T_execution_context)
        env0.assert_expr_is_of_type(bvar, T_execution_context)
        return env0

# ------------------------------------------------------------------------------
#> Evaluation of code by the running execution context
#> may be suspended at various points defined within this specification.

@P("{COMMAND} : Suspend the running execution context.")
class _:
    def s_nv(anode, env0):
        [] = anode.children
        return env0

@P("{COMMAND} : Suspend {var} and remove it from the execution context stack.")
class _:
    def s_nv(anode, env0):
        [var] = anode.children
        env0.assert_expr_is_of_type(var, T_execution_context)
        return env0

@P("{COMMAND} : Suspend {var}.")
class _:
    def s_nv(anode, env0):
        [var] = anode.children
        return env0.ensure_expr_is_of_type(var, T_execution_context)

@P("{SMALL_COMMAND} : suspend {var}")
class _:
    def s_nv(anode, env0):
        [var] = anode.children
        env0.assert_expr_is_of_type(var, T_execution_context)
        return env0

@P("{CONDITION_1} : {var} is not already suspended")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_execution_context)
        return (env0, env0)

# ------
# Resume

# -----------------
# resume-after-push (i.e., resuming an EC that's just been pushed onto the stack):

@P("{COMMAND} : {h_emu_meta_start}Resume the suspended evaluation of {var}{h_emu_meta_end} using {EX} as the result of the operation that suspended it. Let {DEFVAR} be the Completion Record returned by the resumed computation.")
@P("{COMMAND} : {h_emu_meta_start}Resume the suspended evaluation of {var}{h_emu_meta_end} using {EX} as the result of the operation that suspended it. Let {DEFVAR} be the value returned by the resumed computation.")
class _:
    def s_nv(anode, env0):
        [_, ctx_var, _, resa_ex, resb_var] = anode.children
        env0.assert_expr_is_of_type(ctx_var, T_execution_context)
        env1 = env0.ensure_expr_is_of_type(resa_ex, NormalCompletionType(T_Tangible_) | T_return_completion | T_throw_completion)
        return env1.plus_new_entry(resb_var, NormalCompletionType(T_Tangible_) | T_throw_completion)

# ----------------
# resume-after-pop (i.e., resuming an EC that's just been revealed by a stack-pop):

@P("{COMMAND} : {h_emu_meta_start}Resume the suspended evaluation of {var}{h_emu_meta_end} using {EX} as the result of the operation that suspended it.")
class _:
    def s_nv(anode, env0):
        [_, ctx_var, _, resa_ex] = anode.children
        env0.assert_expr_is_of_type(ctx_var, T_execution_context)
        env1 = env0.ensure_expr_is_of_type(resa_ex, NormalCompletionType(T_Tangible_) | T_throw_completion)
        return env1

@P("{COMMAND} : {h_emu_meta_start}Resume the suspended evaluation of {var}{h_emu_meta_end}. Let {DEFVAR} be the value returned by the resumed computation.")
class _:
    def s_nv(anode, env0):
        [_, ctx_var, _, b_var] = anode.children
        env0.assert_expr_is_of_type(ctx_var, T_execution_context)
        return env0.plus_new_entry(b_var, NormalCompletionType(T_Tangible_) | T_return_completion | T_throw_completion)

@P("{COMMAND} : Resume the context that is now on the top of the execution context stack as the running execution context.")
class _:
    def s_nv(anode, env0):
        [] = anode.children
        return env0

@P("{COMMAND} : Resume {var} passing {EX}. If {var} is ever resumed again, let {DEFVAR} be the Completion Record with which it is resumed.")
class _:
    def s_nv(anode, env0):
        [vara, exb, varc, vard] = anode.children
        env0.assert_expr_is_of_type(vara, T_execution_context)
        env1 = env0.ensure_expr_is_of_type(exb, NormalCompletionType(T_Tangible_) | T_throw_completion)
        env1.assert_expr_is_of_type(varc, T_execution_context)
        return env0.plus_new_entry(vard, NormalCompletionType(T_Tangible_ | T_tilde_empty_) | T_throw_completion)


# ------
# other:

@P("{CONDITION_1} : When we return here, {var} has already been removed from the execution context stack and {var} is the currently running execution context")
class _:
    def s_cond(cond, env0, asserting):
        [a_var, b_var] = cond.children
        env0.assert_expr_is_of_type(a_var, T_execution_context)
        env0.assert_expr_is_of_type(b_var, T_execution_context)
        return (env0, env0)

@P("{CONDITION_1} : control reaches here")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

@P("{CONDITION_1} : we return here")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

@P("{CONDITION_1} : When we reach this step, {var} has already been removed from the execution context stack and {var} is the currently running execution context")
class _:
    def s_cond(cond, env0, asserting):
        [vara, varb] = cond.children
        env0.assert_expr_is_of_type(vara, T_execution_context)
        env0.assert_expr_is_of_type(varb, T_execution_context)
        return (env0, env0)

# ------------------------------------------------------------------------------
#> The value of the Realm component of the running execution context
#> is also called <dfn id="current-realm">the current Realm Record</dfn>.

@P("{EX} : the current Realm Record")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_Realm_Record, env0)

# ------------------------------------------------------------------------------
#> The value of the Function component of the running execution context
#> is also called the <dfn>active function object</dfn>.

@P("{LITERAL_ISH} : the active function object")
class _:
    s_tb = a_subset_of(T_function_object_)

    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_function_object_, env0)

# ------------------------------------------------------------------------------
#> <dfn>ECMAScript code execution contexts</dfn>
#> have the additional state components listed in
#> <emu-xref href="#table-additional-state-components-for-ecmascript-code-execution-contexts"></emu-xref>

@P("{EXPR} : a new ECMAScript code execution context")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_execution_context, env0)

# ------------------------------------------------------------------------------
#> Execution contexts representing the evaluation of Generators
#> have the additional state components listed in
#> <emu-xref href="#table-additional-state-components-for-generator-execution-contexts"></emu-xref>.

@P("{VAL_DESC} : the execution context of a generator")
class _:
    s_tb = a_subset_of(T_execution_context)

@P("{CONDITION_1} : {var} does not have a Generator component")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_execution_context)
        return (env0, env0)

# ------------------------------------------------------------------------------

# for 15.10.3 PrepareForTailCall
@P("{CONDITION_1} : The current execution context will not subsequently be used for the evaluation of any ECMAScript code or built-in functions. The invocation of Call subsequent to the invocation of this abstract operation will create and push a new execution context before performing any such evaluation")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

# for 15.10.3 PrepareForTailCall
@P("{COMMAND} : Discard all resources associated with the current execution context.")
class _:
    def s_nv(anode, env0):
        [] = anode.children
        return env0

# ==============================================================================
#@ 9.4.2 ResolveBinding

@P("{PROD_REF} : the syntactic production that is being evaluated")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_Parse_Node, env0)

# ==============================================================================
#@ 9.5 Jobs and Host Operations to Enqueue Jobs

@P("{VAL_DESC} : a Job Abstract Closure")
class _:
    s_tb = T_Job

@P("{VAL_DESC} : a JobCallback Record")
class _:
    s_tb = T_JobCallback_Record

# ==============================================================================
#@ 9.6 InitializeHostDefinedRealm

@P("{CONDITION_1} : the host requires use of an exotic object to serve as {var}'s global object")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_Realm_Record)
        return (env0, env0)

@P("{CONDITION_1} : the host requires that the `this` binding in {var}'s global scope return an object other than the global object")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_Realm_Record)
        return (env0, env0)

@P("{EXPR} : such an object created in a host-defined manner")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_Object, env0)

@P("{COMMAND} : Create any host-defined global object properties on {var}.")
class _:
    def s_nv(anode, env0):
        [var] = anode.children
        env0.assert_expr_is_of_type(var, T_Object)
        return env0

# ==============================================================================
#@ 9.7 Agents

#> An <dfn>agent</dfn> comprises
#> a set of ECMAScript execution contexts,
#> an execution context stack,
#> a running execution context,
#> an <dfn>Agent Record</dfn>, and
#> an <dfn>executing thread</dfn>.
#> Except for the executing thread,
#> the constituents of an agent belong exclusively to that agent.

# Issue #1357 "Define Agent (and Agent Cluster) more concretely":
#> it'd be good to formally define agent as holding:
#>  * A set of Realms. The realms in the set are private to the Agent
#>    and may not be accessible to any other agent.
#>  * A heap of SharedArrayBuffer objects that whose access may be shared with other Agents
#>  * A set of well-known symbol values
#>  * A GlobalSymbolRegistry

class ES_Agent(ES_Value):
    def __init__(self):
        self.frame_stack = []
        self.max_frame_stack_len = 0

# ------------------------------------------------------------------------------
#> While an agent's executing thread executes jobs,
#> the agent is the <dfn>surrounding agent</dfn>
#> for the code in those jobs.

@P("{EXPR} : the Agent Record of the surrounding agent")
@P("{EXPR} : the surrounding agent's Agent Record")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_Agent_Record, env0)

# for 16.2.1.5.2 Evaluate
@P("{CONDITION_1} : This call to Evaluate is not happening at the same time as another call to Evaluate within the surrounding agent")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

# ------------------------------------------------------------------------------
#> An <dfn>agent signifier</dfn> is
#> a globally-unique opaque value used to identify an Agent.

@P("{VAL_DESC} : an agent signifier")
class _:
    s_tb = T_agent_signifier_

# ==============================================================================
#@ 9.10 Processing Model of WeakRef and FinalizationRegistry Targets

# 9.10.4.1
@P("{SMALL_COMMAND} : perform any host-defined steps for reporting the error")
class _:
    def s_nv(anode, env0):
        [] = anode.children
        return env0

# ==============================================================================
#@ 9.13 CleanupFinalizationRegistry

@P("{COMMAND} : Choose any such {var}.")
class _:
    def s_nv(anode, env0):
        [var] = anode.children
        return env0.ensure_expr_is_of_type(var, T_FinalizationRegistryCellRecord_)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 10 Ordinary and Exotic Objects Behaviours

# ==============================================================================
#@ 10.1 Ordinary Object Internal Methods and Internal Slots

declare_isom(T_Object, 'might have', 'slot', '[[Prototype]]',  T_Object | T_Null)
declare_isom(T_Object, 'might have', 'slot', '[[Extensible]]', T_Boolean)

# Exotic objects aren't required to have
# [[Prototype]] and [[Extensible]] internal slots,
# although most spec-defined ones do.
# I think the only kind that doesn't is Proxy.

# ==============================================================================
#@ 10.2 ECMAScript Function Objects

@P("{VAL_DESC} : an ECMAScript function object")
class _:
    s_tb = T_ECMAScript_function_object_

# ==============================================================================
#@ 10.3 Built-in Function Objects

#> The built-in function objects defined in this specification
#> may be implemented as either
#>   ECMAScript function objects (<emu-xref href="#sec-ecmascript-function-objects"></emu-xref>)
#>   whose behaviour is provided using ECMAScript code
#> or as implementation provided function exotic objects
#> whose behaviour is provided in some other manner. [...]
#>
#> If a built-in function object is implemented as an ECMAScript function object,
#> it must have
#> all the internal slots described in
#>   <emu-xref href="#sec-ecmascript-function-objects"></emu-xref>
#>     ([[Prototype]], [[Extensible]], and the slots listed in
#>     <emu-xref href="#table-internal-slots-of-ecmascript-function-objects"></emu-xref>),
#> plus [[InitialName]].
#> The value of the [[InitialName]] internal slot
#> is a String value that is the initial name of the function.
#> It is used by <emu-xref href="#sec-function.prototype.tostring"></emu-xref>.
#>
#> If a built-in function object is implemented as an exotic object,
#> it must have the ordinary object behaviour specified in
#> <emu-xref href="#sec-ordinary-object-internal-methods-and-internal-slots"></emu-xref>.
#> All such function exotic objects have
#> [[Prototype]], [[Extensible]], [[Realm]], and [[InitialName]] internal slots,
#> with the same meanings as above.

declare_isom(T_built_in_function_object_, 'must have', 'slot', '[[Realm]]',       T_Realm_Record)
declare_isom(T_built_in_function_object_, 'must have', 'slot', '[[InitialName]]', T_Null | T_String)

#> If a built-in function object is not implemented as an ECMAScript function
#> it must provide [[Call]] and [[Construct]] internal methods that conform to the following definitions:
#>  - #sec-built-in-function-objects-call-thisargument-argumentslist
#>  - #sec-built-in-function-objects-construct-argumentslist-newtarget

@P("{VAL_DESC} : a built-in function object")
class _:
    s_tb = T_built_in_function_object_

@P("{EX} : *this* value")
@P("{EX} : the *this* value")
class _:
    def s_expr(expr, env0, _):
        return (T_Tangible_, env0)

@P("{EX} : NewTarget")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_constructor_object_ | T_Undefined, env0)

# SPEC BUG:
# A class-constructor-function
# (the _F_ identified in and returned by ClassDefinitionEvaluation)
# can be
# - an ECMAScript function object, or
# - a built-in function that isn't an ECMAScript function object
#   (if |ClassBody| doesn't have a ConstructorMethod),
#
# but a couple places don't handle the latter alternative well:
#
# - InitializeInstanceElements asserts that its _constructor_ parameter
#   is an ECMAScript function object, which is not necessarily true
#   for the invocation in ClassDefinitionEvaluation.
#
# - ClassDefinitionEvaluation sets _F_.[[PrivateMethods]] and _F_.[[Fields]],
#   but a built-in function doesn't have those internal slots.
#
#   The relevant call to CreateBuiltinFunction specifies to create slots
#   [[ConstructorKind]] and [[SourceText]]:
declare_isom(T_built_in_function_object_, 'might have', 'slot', '[[ConstructorKind]]', T_tilde_base_ | T_tilde_derived_)
declare_isom(T_built_in_function_object_, 'might have', 'slot', '[[SourceText]]',      T_Unicode_code_points_)

#   but it should presumably also specify [[PrivateMethods]] and [[Fields]]:
declare_isom(T_built_in_function_object_, 'might have', 'slot', '[[PrivateMethods]]',  ListType(T_PrivateElement))
declare_isom(T_built_in_function_object_, 'might have', 'slot', '[[Fields]]',          ListType(T_ClassFieldDefinition_Record))

declare_isom(T_constructor_object_, 'must have', 'slot', '[[ConstructorKind]]', T_tilde_base_ | T_tilde_derived_)

# ==============================================================================
#@ 10.3.3 BuiltinCallOrConstruct

@P("{EXPR} : the Completion Record that is {h_emu_meta_start}the result of evaluating{h_emu_meta_end} {var} in a manner that conforms to the specification of {var}. If {CONDITION}, the *this* value is uninitialized; otherwise, {var} provides the *this* value. {var} provides the named parameters. {var} provides the NewTarget value")
class _:
    def s_expr(expr, env0, _):
        [_, _, avar, bvar, cond, cvar, dvar, evar] = expr.children
        assert avar.children == bvar.children
        env0.assert_expr_is_of_type(avar, T_function_object_)
        env0.assert_expr_is_of_type(cvar, T_Tangible_ | T_tilde_uninitialized_)
        env0.assert_expr_is_of_type(dvar, ListType(T_Tangible_))
        env0.assert_expr_is_of_type(evar, T_constructor_object_ | T_Undefined)
        return (NormalCompletionType(T_Tangible_) | T_throw_completion, env0)

# ==============================================================================
#@ 10.3.4 CreateBuiltinFunction

@P("{VAL_DESC} : a set of algorithm steps")
class _:
    s_tb = T_alg_steps

@P("{EXPR} : the algorithm steps defined in {h_emu_xref}")
class _:
    def s_expr(expr, env0, _):
        [emu_xref] = expr.children
        return (T_alg_steps, env0)

# ------------------------------------------------------------------------------

@P("{VAL_DESC} : some other definition of a function's behaviour provided in this specification")
class _:
    s_tb = T_alg_steps

# ------------------------------------------------------------------------------

@P("{EXPR} : a List containing the names of all the internal slots that {h_emu_xref} requires for the built-in function object that is about to be created")
class _:
    def s_expr(expr, env0, _):
        [xref] = expr.children
        return (ListType(T_SlotName_), env0)

@P("{EXPR} : a new built-in function object that, when called, performs the action described by {var} using the provided arguments as the values of the corresponding parameters specified by {var}. The new function object has internal slots whose names are the elements of {var}, and an {DSBN} internal slot")
class _:
    def s_expr(expr, env0, _):
        [var1, var2, var3, dsbn] = expr.children
        env1 = env0.ensure_expr_is_of_type(var1, T_proc_ | T_alg_steps)
        # env1 = env0.ensure_expr_is_of_type(var2, )
        return (T_built_in_function_object_, env1)

# ==============================================================================
#@ 10.4.1 Bound Function Exotic Objects

@P("{VAL_DESC} : a bound function exotic object")
class _:
    s_tb = T_bound_function_exotic_object_

# ==============================================================================
#@ 10.4.2 Array Exotic Objects

#> An object is an <dfn>Array exotic object</dfn> (or simply, an Array)
#> if its [[DefineOwnProperty]] internal method uses the following implementation,
#> and its other essential internal methods use the definitions found in
#> <emu-xref href="#sec-ordinary-object-internal-methods-and-internal-slots"></emu-xref>.
#> These methods are installed in ArrayCreate.

@P("{VAL_DESC} : an Array")
@P("{VAL_DESC} : an Array exotic object")
class _:
    s_tb = T_Array_object_

# ==============================================================================
#@ 10.4.3 String Exotic Objects

#> An object is a <dfn>String exotic object</dfn> (or simply, a String object)
#> if its [[GetOwnProperty]], [[DefineOwnProperty]], and [[OwnPropertyKeys]] internal methods
#> use the following implementations,
#> and its other essential internal methods use the definitions found in
#> <emu-xref href="#sec-ordinary-object-internal-methods-and-internal-slots"></emu-xref>.
#> These methods are installed in StringCreate.
#>
#> String exotic objects have the same internal slots as ordinary objects.
#> They also have a [[StringData]] internal slot.

@P("{VAL_DESC} : a String exotic object")
class _:
    s_tb = T_String_exotic_object_

# ==============================================================================
#@ 10.4.4 Arguments Exotic Objects

#> An object is an <dfn>arguments exotic object</dfn>
#> if its internal methods use the following implementations,
#> with the ones not specified here using those found in
#> <emu-xref href="#sec-ordinary-object-internal-methods-and-internal-slots"></emu-xref>.
#> These methods are installed in CreateMappedArgumentsObject.

@P("{VAL_DESC} : an arguments exotic object")
class _:
    s_tb = a_subset_of(T_Object)

declare_isom(T_Object, 'might have', 'slot', '[[ParameterMap]]', T_Object)

# for 10.4.4.{2,4}
@P("{CONDITION_1} : The following Set will succeed, since formal parameters mapped by arguments objects are always writable")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

# for 10.4.4.3
@P("{CONDITION_1} : {EX} contains a formal parameter mapping for {var}")
class _:
    def s_cond(cond, env0, asserting):
        [avar, bvar] = cond.children
        env0.assert_expr_is_of_type(avar, T_Object)
        env0.assert_expr_is_of_type(bvar, T_String | T_Symbol)
        return (env0, env0)

# ==============================================================================
#@ 10.4.4.7 CreateMappedArgumentsObject

@P("{CONDITION_1} : {var} does not contain a rest parameter, any binding patterns, or any initializers. It may contain duplicate identifiers")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        return (env0, env0)

# ==============================================================================
#@ 10.4.5 TypedArray Exotic Objects

#> <emu-xref>TypedArray exotic objects</emu-xref>
#> have the same internal slots as ordinary objects and additionally
#> [[ViewedArrayBuffer]],
#> [[ArrayLength]],
#> [[ByteOffset]],
#> [[ContentType]], and
#> [[TypedArrayName]] internal slots.

# (SPEC BUG: That list is missing [[ByteLength]], see TypedArrayCreate.)

declare_isom(T_TypedArray_object_, 'must have', 'slot', '[[ViewedArrayBuffer]]', T_ArrayBuffer_object_ | T_SharedArrayBuffer_object_)
declare_isom(T_TypedArray_object_, 'must have', 'slot', '[[ArrayLength]]',       T_MathNonNegativeInteger_ | T_tilde_auto_)
declare_isom(T_TypedArray_object_, 'must have', 'slot', '[[ByteOffset]]',        T_MathNonNegativeInteger_)
declare_isom(T_TypedArray_object_, 'must have', 'slot', '[[ContentType]]',       T_tilde_bigint_ | T_tilde_number_)
declare_isom(T_TypedArray_object_, 'must have', 'slot', '[[TypedArrayName]]',    T_String)
declare_isom(T_TypedArray_object_, 'must have', 'slot', '[[ByteLength]]',        T_MathNonNegativeInteger_ | T_tilde_auto_)

# ==============================================================================
#@ 10.4.5.8 TypedArray With Buffer Witness Records

@P("{VAL_DESC} : a TypedArray With Buffer Witness Record")
class _:
    s_tb = T_TypedArray_With_Buffer_Witness_Record

# ==============================================================================
#@ 10.4.6 Module Namespace Exotic Objects

@P("{VAL_DESC} : a module namespace exotic object")
class _:
    s_tb = T_module_namespace_exotic_object_

#@ 10.4.6.12 ModuleNamespaceCreate
@P("{COMMAND} : Create own properties of {var} corresponding to the definitions in {h_emu_xref}.")
class _:
    def s_nv(anode, env0):
        [var, emu_xref] = anode.children
        env0.assert_expr_is_of_type(var, T_module_namespace_exotic_object_)
        return env0

# ==============================================================================
# 10.5 Proxy Object Internal Methods and Internal Slots

#> A Proxy object is an exotic object
#> whose essential internal methods
#> are partially implemented using ECMAScript code.

@P("{VAL_DESC} : a Proxy exotic object")
class _:
    s_tb = T_Proxy_exotic_object_

#> Every Proxy object has an internal slot called [[ProxyHandler]].
#> The value of [[ProxyHandler]] is an object,
#> called the proxy's <em>handler object</em>, or *null*.
#> Methods (see <emu-xref href="#table-proxy-handler-methods"></emu-xref>) of a handler object
#> may be used to augment the implementation for one or more of the Proxy object's internal methods.

declare_isom(T_Proxy_exotic_object_, 'must have', 'slot', '[[ProxyHandler]]', T_Object | T_Null)

#> Every Proxy object also has an internal slot called [[ProxyTarget]]
#> whose value is either an object or the *null* value.
#> This object is called the proxy's <em>target object</em>.<

declare_isom(T_Proxy_exotic_object_, 'must have', 'slot', '[[ProxyTarget]]',  T_Object | T_Null)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 11 ECMAScript Language: Source Text

# ==============================================================================
#@ 11.1 Source Text

#> <dfn>ECMAScript source text</dfn> is a sequence of Unicode code points.
#> All Unicode code point values from U+0000 to U+10FFFF,
#> including surrogate code points, may occur in source text ...

# ==============================================================================
#@ 11.1.6 Static Semantics: ParseText

@P("{COMMAND} : Attempt to parse {var} using {var} as the goal symbol, and analyse the parse result for any early error conditions. Parsing and early error detection may be interleaved in an implementation-defined manner.")
class _:
    def s_nv(anode, env0):
        [text_var, goal_var] = anode.children
        env0.assert_expr_is_of_type(text_var, T_Unicode_code_points_)
        env0.assert_expr_is_of_type(goal_var, T_grammar_symbol_)
        return env0

    def d_exec(command):
        [subject_var, goal_var] = command.children
        subject = EXEC(subject_var, ES_UnicodeCodePoints)
        goal_sym = EXEC(goal_var, ES_NonterminalSymbol)
        frame = curr_frame()
        try:
            frame.kludge_node = parse(subject.text, goal_sym.name)
        except ParseError as e:
            frame.kludge_node = None
            frame.kludge_errors = [e]
            return
        frame.kludge_errors = get_early_errors_in(frame.kludge_node)

@P("{CONDITION_1} : the parse succeeded and no early errors were found")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

    def d_exec(cond):
        [] = cond.children
        frame = curr_frame()
        return (
            frame.kludge_node is not None
            and
            frame.kludge_errors == []
        )

@P("{EXPR} : the Parse Node (an instance of {var}) at the root of the parse tree resulting from the parse")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_grammar_symbol_)
        return (T_Parse_Node, env0)

    def d_exec(expr):
        [var] = expr.children
        gsym = EXEC(var, ES_GrammarSymbol)
        frame = curr_frame()
        assert (
            frame.kludge_node is not None
            and
            frame.kludge_errors == []
        )
        return frame.kludge_node

@P("{EXPR} : a List of one or more {ERROR_TYPE} objects representing the parsing errors and/or early errors. If more than one parsing error or early error is present, the number and ordering of error objects in the list is implementation-defined, but at least one must be present")
@P("{EXPR} : a List containing one or more {ERROR_TYPE} objects")
class _:
    def s_expr(expr, env0, _):
        [error_type] = expr.children
        return (ListType(type_for_ERROR_TYPE(error_type)), env0)

    def d_exec(expr):
        [error_type] = expr.children
        assert error_type.source_text() == '*SyntaxError*'
        frame = curr_frame()
        assert frame.kludge_errors
        objects = [
            # TODO: make a SyntaxError object!
            EL_Object([])
            # ee.kind, ee.location, ee.condition
            for ee in frame.kludge_errors
        ]
        return ES_List(objects)

# ==============================================================================
#@ 11.2.1 Directive Prologues and the Use Strict Directive

@P("{CONDITION_1} : the Directive Prologue of {PROD_REF} contains a Use Strict Directive")
class _:
    def s_cond(cond, env0, asserting):
        [prod_ref] = cond.children
        env0.assert_expr_is_of_type(prod_ref, T_Parse_Node)
        return (env0, env0)

    def d_exec(cond):
        [prod_ref] = cond.children
        pnode = EXEC(prod_ref, ES_ParseNode)
        return begins_with_a_DP_that_contains_a_USD(pnode)

# ==============================================================================
#@ 11.2.2 Strict Mode Code

@P("{CONDITION_1} : the source text matched by {var} is strict mode code")
class _:
    def s_cond(cond, env0, asserting):
        [local_ref] = cond.children
        env0.assert_expr_is_of_type(local_ref, T_Parse_Node)
        return (env0, env0)

    def d_exec(cond):
        [local_ref] = cond.children
        pnode = EXEC(local_ref, ES_ParseNode)
        return is_strict(pnode)

# ------------------------------------------------------------------------------

def is_strict(pnode):
    # {pnode} matches code that is contained in strict mode code iff:
    # - {pnode} is inherently strict, or
    # - {pnode} explicitly declares that it is strict (via a Use Strict Directive), or
    # - {pnode} inherits strictness from "outside".
    # But these are somewhat blended in the spec's definition of strictness.

    # print('is_strict:', pnode.text(), f"<{pnode.symbol}>")

    #> Module code is always strict mode code.
    #> All parts of a ClassDeclaration or a ClassExpression are strict mode code.
    if pnode.symbol in [
        'ModuleBody',
        'ClassDeclaration',
        'ClassExpression',
    ]:
        return True

    #> Global code is strict mode code if
    #> it begins with a Directive Prologue that contains a Use Strict Directive. 
    #>
    #> Eval code is strict mode code if
    #> it begins with a Directive Prologue that contains a Use Strict Directive
    #> or if
    #> the call to eval is a direct eval that is contained in strict mode code. 
    elif pnode.symbol == 'Script':
        if begins_with_a_DP_that_contains_a_USD(pnode):
            return True

        # XXX eval:
        # if pnode.is_the_result_of_parsing_source_text_supplied_to_the_built_in_eval
        # and
        # the_call_to_eval_is_a_direct_eval_that_is_contained_in_strict_mode_code:
        #     return True

    #> Function code is strict mode code if
    #> the associated [definition] is contained in strict mode code or if
    #> the code that produces the value of the function's [[ECMAScriptCode]] internal slot
    #> begins with a Directive Prologue that contains a Use Strict Directive. 
    elif pnode.symbol in [
        'FunctionDeclaration',
        'FunctionExpression',
        'GeneratorDeclaration',
        'GeneratorExpression',
        'AsyncFunctionDeclaration',
        'AsyncFunctionExpression',
        'AsyncGeneratorDeclaration',
        'AsyncGeneratorExpression',
        'MethodDefinition',
        'ArrowFunction',
        'AsyncArrowFunction',
    ]:
        # the code that produces the value of the function's [[ECMAScriptCode]] internal slot:
        if pnode.symbol in ['ArrowFunction', 'AsyncArrowFunction']:
            body = pnode.children[-1]
            assert body.symbol in ['ConciseBody', 'AsyncConciseBody']
        elif pnode.symbol == 'MethodDefinition':
            if len(pnode.children) == 1:
                [cnode] = pnode.children
                assert cnode.symbol in ['GeneratorMethod', 'AsyncMethod', 'AsynGeneratorMethod']
                body = cnode.children[-2]
                assert body.symbol in ['GeneratorBody', 'AsyncFunctionBody', 'AsyncGeneratorBody']
            else:
                body = pnode.children[-2]
                assert body.symbol == 'FunctionBody'
        else:
            body = pnode.children[-2]
            assert body.symbol in ['FunctionBody', 'GeneratorBody']

        if begins_with_a_DP_that_contains_a_USD(body):
            return True

    #> Function code that is supplied as the arguments to the built-in
    #> Function, Generator, AsyncFunction, and AsyncGenerator constructors
    #> is strict mode code if
    #> the last argument is a String that when processed is a FunctionBody
    #> that begins with a Directive Prologue that contains a Use Strict Directive.

    # i.e., code supplied to the _args_ parameter of CreateDynamicFunction
    # Step 20.e detects the condition

    if pnode.parent is None:
        # {pnode} is the root of its parse tree.

        if pnode.symbol in ['FormalParameters', 'UniqueFormalParameters']:
            assert NYI

        if hasattr(pnode, 'covering_thing'):
            if is_strict(pnode.covering_thing): return True

    else:
        if is_strict(pnode.parent): return True

    return False

def begins_with_a_DP_that_contains_a_USD(pnode):
    #> A `Directive Prologue` is the longest sequence of |ExpressionStatement|s
    #> occurring as the initial |StatementListItem|s or |ModuleItem|s
    #> of a |FunctionBody|, a |ScriptBody|, or a |ModuleBody|
    #> and where each |ExpressionStatement| in the sequence consists entirely of
    #> a |StringLiteral| token followed by a semicolon.
    #> The semicolon may appear explicitly or may be inserted by automatic semicolon insertion.
    #> A Directive Prologue may be an empty sequence.

    def has_the_shape_of_a_Directive_Prologue_item(item_node):
        assert item_node.symbol in ['StatementListItem', 'ModuleItem']
        if ExpressionStatement := item_node.unit_derives_a('ExpressionStatement'):
            [Expression, semicolon] = ExpressionStatement.children
            if StringLiteral := Expression.unit_derives_a('StringLiteral'):
                return StringLiteral

        return None

    assert pnode.symbol in ['Script', 'ModuleBody', 'FunctionBody', 'GeneratorBody', 'ConciseBody', 'AsyncConciseBody']

    if pnode.symbol == 'ModuleBody':
        assert NYI
        return False

    if pnode.symbol in ['ConciseBody', 'AsyncConciseBody']:
        if len(pnode.children) == 1:
            assert pnode.children[0].symbol == 'ExpressionBody'
            # An ExpressionBody can't have a Directive Prologue.
            return False

        elif len(pnode.children) == 3:
            fnbody = pnode.children[1]
            assert fnbody.symbol in ['FunctionBody', 'AsyncFunctionBody']
            pnode = fnbody

        else:
            assert 0

    assert pnode.symbol in ['Script', 'FunctionBody', 'GeneratorBody']

    StatementList = pnode.unit_derives_a('StatementList')
    if StatementList is None: return False

    for item_node in each_item_in_left_recursive_list(StatementList):
        assert item_node.symbol == 'StatementListItem'
        if StringLiteral := has_the_shape_of_a_Directive_Prologue_item(item_node):
            #> A `Use Strict Directive` is an |ExpressionStatement| in a Directive Prologue
            #> whose |StringLiteral| is either of the exact code point sequences `"use strict"` or `'use strict'`.
            #> A Use Strict Directive may not contain an |EscapeSequence| or |LineContinuation|.
            if StringLiteral.text() in ['"use strict"', "'use strict'"]:
                return True
        else:
            # We are past the end of the Directive Prologue,
            # so stop looking for a USD.
            break

    return False

def each_item_in_left_recursive_list(list_node):
    assert list_node.isan(ES_ParseNode)
    assert list_node.symbol.endswith('List')
    n_children = len(list_node.children)
    if n_children == 1:
        [item_node] = list_node.children
        assert item_node.symbol.endswith('Item')
        yield item_node
    elif n_children == 2:
        [sublist_node, item_node] = list_node.children
        assert sublist_node.symbol.endswith('List')
        assert item_node.symbol.endswith('Item')
        yield from each_item_in_left_recursive_list(sublist_node)
        yield item_node
    else:
        assert 0

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 12 ECMAScript Language: Lexical Grammar

#> The source text of an ECMAScript Script or Module
#> is first converted into a sequence of input elements,
#> which are tokens, line terminators, comments, or white space.
#> The source text is scanned from left to right,
#> repeatedly taking the longest possible sequence of code points
#> as the next input element.

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 13 ECMAScript Language: Expressions

# ==============================================================================
#@ 13.1.1 Static Semantics: Early Errors [for Identifiers]

@P("{CONDITION_1} : {NAMED_OPERATION_INVOCATION} is the StringValue of any |ReservedWord| except for `yield` or `await`")
class _:
    def s_cond(cond, env0, asserting):
        [noi] = cond.children
        env0.assert_expr_is_of_type(noi, T_String)
        return (env0, env0)

    def d_exec(cond):
        [noi] = cond.children
        st = EXEC(noi, EL_String)

        reserved_word_set = set()
        g = spec.grammar_[('syntactic', 'A')]
        for rhs in g.prodn_for_lhs_['ReservedWord']._rhss:
            assert rhs.kind == 'BACKTICKED_THING'
            # Theoretically, I should apply StringValue,
            # except that's a bit slippery.
            # StringValue is defined on ParseNodes
            # (specifically, instances of |Identifier| and similar)
            # whereas "any |ReservedWord|" is just looking at symbols in the grammar.
            reserved_word_set.add(rhs._chars)
        target_set = reserved_word_set - {'yield', 'await'}

        return (st.to_Python_String() in target_set)

# ==============================================================================
#@ 13.2.5.1 Static Semantics: Early Errors

@P("{CONDITION_1} : {EX} contains any duplicate entries for {starred_str} and at least two of those entries were obtained from productions of the form {h_emu_grammar}")
class _:
    def s_cond(cond, env0, asserting):
        [noi, ss, emu_grammar] = cond.children
        env1 = env0.ensure_expr_is_of_type(noi, ListType(T_String))
        return (env1, env1)

    def d_exec(cond):
        [noi, ss, h_emu_grammar] = cond.children
        L = EXEC(noi, ES_List)
        v = EXEC(ss, E_Value)
        if L.number_of_occurrences_of(v) <= 1: return False

        # Okay, so we know that {L} contains duplicate entries for {v}.
        # But the second part of the condition is weird,
        # because it's asking *after the fact*
        # about how the entries in {L} were obtained.
        # (The 'proper' way to do this would be to modify the rules involved,
        # or make a new SDO, to compute the quantity of interest.)

        assert noi.source_text() == 'PropertyNameList of |PropertyDefinitionList|'

        PDL = curr_frame().resolve_focus_reference(None, 'PropertyDefinitionList')

        def each_PD_in_PDL(PDL):
            assert PDL.symbol == 'PropertyDefinitionList'
            r = PDL.production.og_rhs_reduced
            if r == 'PropertyDefinition':
                [PD] = PDL.children
                yield PD
            elif r == 'PropertyDefinitionList `,` PropertyDefinition':
                [PDL, _, PD] = PDL.children
                yield from each_PD_in_PDL(PDL)
                yield PD
            else:
                assert 0

        n = 0
        for PD in each_PD_in_PDL(PDL):
            assert PD.symbol == 'PropertyDefinition'
            propName = execute_sdo_invocation('PropName', PD, [])
            if same_value(propName, v):
                # This is one of the duplicate entries.
                # Was it obtained from a production of the given form?
                # SPEC BUG: s/production/Parse Node/
                if PD.puk in h_emu_grammar._hnode.puk_set:
                    # Yes, it was.
                    n += 1

        return (n >= 2)

# ==============================================================================
#@ 13.3.6.1 Runtime Semantics: Evaluation [of Function Calls]

#> A |CallExpression| evaluation that executes step
#> <emu-xref href="#step-callexpression-evaluation-direct-eval"></emu-xref>
#> is a <dfn>direct eval</dfn>

@P("{CONDITION_1} : the source text containing {G_SYM} is eval code that is being processed by a direct eval")
class _:
    def s_cond(cond, env0, asserting):
        [g_sym] = cond.children
        return (env0, env0)

    def d_exec(cond):
        [gsym] = cond.children
        return False # TODO

# ==============================================================================
#@ 13.15.2 Runtime Semantics: Evaluation [of Assignment Operators]

# for PR #1961 compound_assignment
@P("{MULTILINE_EXPR} : the {TABLE_RESULT_TYPE} associated with {var} in the following table:{_indent_}{nlai}{h_figure}{_outdent_}")
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

@P("{MULTILINE_EXPR} : the {TABLE_RESULT_TYPE} associated with {var} and Type({var}) in the following table:{_indent_}{nlai}{h_figure}{_outdent_}")
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

@P("{CONDITION_1} : {var} binds a single name")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        return (env0, env0)

# ==============================================================================
#@ 14.7.5.10 For-In Iterator Objects

@P("{VAL_DESC} : a For-In Iterator")
class _:
    s_tb = T_Iterator_object_

# ==============================================================================
#@ 14.12.2 Runtime Semantics: CaseBlockEvaluation

@P("{PROD_REF} : {nonterminal} {var}")
class _:
    def s_expr(expr, env0, _):
        [nonterminal, var] = expr.children
        t = ptn_type_for(nonterminal)
        env0.assert_expr_is_of_type(var, t)
        return (t, env0)

# ==============================================================================
#@ 14.16 The `debugger` Statement

@P("{CONDITION_1} : an implementation-defined debugging facility is available and enabled")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

@P("{COMMAND} : Perform an implementation-defined debugging action.")
class _:
    def s_nv(anode, env0):
        [] = anode.children
        return env0

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 15 ECMAScript Language: Functions and Classes

# ==============================================================================
#@ 15.7.1 Static Semantics: Early Errors [for Class Definitions]

@P("{CONDITION_1} : the name is used once for a getter and once for a setter and in no other entries, and the getter and setter are either both static or both non-static")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

# ==============================================================================
#@ 15.7.11 Runtime Semantics: ClassStaticBlockDefinitionEvaluation

@P('{VAL_DESC} : a synthetic function created by ClassStaticBlockDefinitionEvaluation step {h_emu_xref}')
class _:
    s_tb = a_subset_of(T_function_object_)

# ==============================================================================
#@ 15.7.14 Runtime Semantics: ClassDefinitionEvaluation

@P("{CONDITION_1} : This is only possible for getter/setter pairs")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

@P("{EXPR} : the List of arguments that was passed to this function by {dsb_word} or {dsb_word}")
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

@P("{VAL_DESC} : a Script Record")
class _:
    s_tb = T_Script_Record

# ==============================================================================
#@ 16.2.1.4 Abstract Module Records

@P("{VAL_DESC} : a Module Record")
class _:
    s_tb = T_Module_Record

@P("{VAL_DESC} : an instance of a concrete subclass of Module Record")
class _:
    s_tb = T_Module_Record

@P("{CONDITION_1} : {SETTABLE} and {SETTABLE} are the same Module Record")
@P("{CONDITION_1} : {SETTABLE} and {SETTABLE} are not the same Module Record")
class _:
    def s_cond(cond, env0, asserting):
        return s_X_and_Y_are_the_same_Foo_Record(cond, T_Module_Record, env0)

@P("{VAL_DESC} : a ResolvedBinding Record")
class _:
    s_tb = T_ResolvedBinding_Record

# ==============================================================================
#@ 16.2.1.5 Cyclic Module Records

@P("{VAL_DESC} : a Cyclic Module Record")
@P("{LIST_ELEMENTS_DESCRIPTION} : Cyclic Module Records")
class _:
    s_tb = T_Cyclic_Module_Record

@P("{VAL_DESC} : a GraphLoadingState Record")
class _:
    s_tb = T_GraphLoadingState_Record

# ==============================================================================
#@ 16.2.1.5.1.1 InnerModuleLoading

@P("{EXPR} : that Record")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        rt = RecordType('', (
                ('[[Specifier]]', T_String),
                ('[[Module]]'   , T_Module_Record),
            )
        )
        return (rt, env0)

# ==============================================================================
#@ 16.2.1.5.3.1 InnerModuleEvaluation

@P("{CONDITION_1} : {DOTTING} is {LITERAL} and was never previously set to {LITERAL}")
class _:
    def s_cond(cond, env0, asserting):
        [dotting, lita, litb] = cond.children
        assert lita.source_text() == '*false*'
        assert litb.source_text() == '*true*'
        env0.assert_expr_is_of_type(dotting, T_Boolean)
        return (env0, env0)

# ==============================================================================
#@ 16.2.1.5.3.4 AsyncModuleExecutionFulfilled

@P("{EXPR} : a List whose elements are the elements of {var}, in the order in which they had their {dsb_word} fields set to {LITERAL} in {cap_word}")
class _:
    def s_expr(expr, env0, _):
        [var, dsb_word, literal, cap_word] = expr.children
        assert dsb_word.source_text() == '[[AsyncEvaluation]]'
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_Cyclic_Module_Record))
        return (ListType(T_Cyclic_Module_Record), env1)

# ==============================================================================
#@ 16.2.1.6 Source Text Module Records

@P("{VAL_DESC} : a Source Text Module Record")
@P("{LIST_ELEMENTS_DESCRIPTION} : Source Text Module Records")
class _:
    s_tb = T_Source_Text_Module_Record

@P("{LIST_ELEMENTS_DESCRIPTION} : ImportEntry Records")
class _:
    s_tb = T_ImportEntry_Record

@P("{LIST_ELEMENTS_DESCRIPTION} : ExportEntry Records")
class _:
    s_tb = T_ExportEntry_Record

@P("{CONDITION_1} : {var} provides the direct binding for this export")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_Source_Text_Module_Record)
        return (env0, env0)

@P("{CONDITION_1} : {var} imports a specific binding for this export")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_Source_Text_Module_Record)
        return (env0, env0)

#@ 16.2.1.6.2 GetExportedNames
@P("{CONDITION_1} : We've reached the starting point of an `export *` circularity")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

# ==============================================================================
#@ 16.2.1.6.3 ResolveExport

@P("{CONDITION_1} : This is a circular import request")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

@P("{CONDITION_1} : A `default` export was not explicitly defined by this module")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

@P("{CONDITION_1} : There is more than one `*` import that includes the requested name")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

@P("{CONDITION_1} : {var} does not provide the direct binding for this export")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_Module_Record)
        return (env0, env0)

# ==============================================================================
#@ 16.2.1.6.4 InitializeEnvironment

@P("{CONDITION_1} : All named exports from {var} are resolvable")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_Source_Text_Module_Record)
        return (env0, env0)

# ==============================================================================
#@ 16.2.1.6.5 ExecuteModule

@P("{CONDITION_1} : {var} has been linked and declarations in its module environment have been instantiated")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_Source_Text_Module_Record)
        return (env0, env0)

# ==============================================================================
#@ 16.2.1.7 GetImportedModule

@P("{CONDITION_1} : LoadRequestedModules has completed successfully on {var} prior to invoking this abstract operation")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_Cyclic_Module_Record)
        return (env0, env0)

# ==============================================================================
#@ 16.2.1.8 HostLoadImportedModule

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 17 Error Handling and Language Extensions

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 18 ECMAScript Standard Built-in Objects

@P("{CONDITION_1} : only one argument was passed")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 19 The Global Object

# for 9.3.4 SetDefaultGlobalBindings
@P("{EACH_THING} : property of the Global Object specified in clause {h_emu_xref}")
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

@P("{EXPR} : an implementation-defined String source code representation of {var}. The representation must have the syntax of a {nonterminal}")
class _:
    def s_expr(expr, env0, _):
        [var, nont] = expr.children
        env0.assert_expr_is_of_type(var, T_function_object_)
        return (T_String, env0)

# ==============================================================================
#@ 20.3 Boolean Objects

declare_isom(T_Object, 'might have', 'slot', '[[BooleanData]]', T_Boolean)

# ==============================================================================
#@ 20.4 Symbol Objects

declare_isom(T_Object, 'might have', 'slot', '[[SymbolData]]', T_Symbol)

# ==============================================================================
#@ 20.4.2.2 Symbol.for

@P("{EX} : the GlobalSymbolRegistry List")
class _:
    def s_expr(expr, env0, _):
        return (ListType(T_GlobalSymbolRegistry_Record), env0)

@P("{CONDITION_1} : GlobalSymbolRegistry does not currently contain an entry for {var}")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_String | T_Symbol)
        return (env0, env0)

# ==============================================================================
#@ 20.5 Error Objects

@P("{LIST_ELEMENTS_DESCRIPTION} : {ERROR_TYPE} objects")
class _:
    def s_tb(led, env):
        [error_type] = led.children
        return type_for_ERROR_TYPE(error_type)

@P("{LIST_ELEMENTS_DESCRIPTION} : errors")
class _:
    s_tb = T_SyntaxError | T_ReferenceError

@P("{EX} : a newly created {ERROR_TYPE} object")
class _:
    def s_expr(expr, env0, _):
        [error_type] = expr.children
        return (type_for_ERROR_TYPE(error_type), env0)

# 20.5.1.1 Error
# 20.5.4   Properties of Error Instances

declare_isom(T_Error, 'must have', 'slot', '[[ErrorData]]', T_Undefined)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 21 Numbers and Dates

# ==============================================================================
#@ 21.1 Number Objects

declare_isom(T_Object, 'might have', 'slot', '[[NumberData]]', T_Number)

# ==============================================================================
#@ 21.2 BigInt Objects

declare_isom(T_Object, 'might have', 'slot', '[[BigIntData]]', T_BigInt)

# ==============================================================================
#@ 21.4 Date Objects

# ==============================================================================
#@ 21.4.1.1 Time Values and Time Range

@P("{VAL_DESC} : a time value")
class _:
    s_tb = T_IntegralNumber_

@P("{VAL_DESC} : a finite time value")
class _:
    s_tb = T_IntegralNumber_

# Time value is defined to be 'IntegralNumber_ | NaN_Number_',
# but the only use is for UTC()'s return value,
# which is the result of a subtraction,
# so probably shouldn't be NaN.
# So I've translated it as T_IntegralNumber_.
# I.e., the spec should say "a *finite* time value".

# ==============================================================================
#@ 21.4.1.2 Time-related Constants

# All of the uses of <emu-eqn> to define named constants
# appear within this section.

@P("{FACTOR} : {CONSTANT_NAME}")
@P("{EX} : {CONSTANT_NAME}")
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
#@ 21.4.1.19 Time Zone Identifiers

@P("{VAL_DESC} : a non-primary time zone identifier in this implementation")
class _:
    s_tb = a_subset_of(T_String)

@P("{EXPR} : the primary time zone identifier associated with {var}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_String)
        return (T_String, env0)

@P("{EXPR} : the List of unique available named time zone identifiers")
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
#@ 21.4.1.22 Time Zone Identifier Record

@P("{VAL_DESC} : a Time Zone Identifier Record")
@P("{LIST_ELEMENTS_DESCRIPTION} : Time Zone Identifier Records")
class _:
    s_tb = T_Time_Zone_Identifier_Record

# ==============================================================================
#@ 21.4.1.23 AvailableNamedTimeZoneIdentifiers

@P("{CONDITION_1} : the implementation does not include local political rules for any time zones")
@P("{CONDITION_1} : the implementation only supports the UTC time zone")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

@P("{COMMAND} : Sort {var} into the same order as if an Array of the same values had been sorted using {percent_word} with {LITERAL} as {var}.")
class _:
    def s_nv(anode, env0):
        [list_var, pc_word, comparefn_lit, comparefn_var] = anode.children
        env0.assert_expr_is_of_type(list_var, ListType(T_String))
        return env0

# ==============================================================================
#@ 21.4.1.26 UTC

@P("{EX} : the largest integral Number &lt; {var} for which {CONDITION_1} (i.e., {var} represents the last local time before the transition)")
class _:
    def s_expr(expr, env0, _):
        [vara, cond, varb] = expr.children
        # (t_env, f_env) = tc_cond(cond, env0)
        # refers to _possibleInstantsBefore_ which hasn't been defined yet, it's complicated
        return (T_IntegralNumber_, env0)

# ==============================================================================
#@ 21.4.1.28 MakeDay

@P("{COMMAND} : Find a finite time value {DEFVAR} such that {CONDITION}; but if this is not possible (because some argument is out of range), return {LITERAL}.")
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

declare_isom(T_Object, 'might have', 'slot', '[[DateValue]]', T_IntegralNumber_ | T_NaN_Number_)

# ==============================================================================
#@ 21.4.2.1 Date

@P("{EXPR} : the time value (UTC) identifying the current time")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_IntegralNumber_, env0)

@P("{EXPR} : the result of parsing {var} as a date, in exactly the same manner as for the `parse` method ({h_emu_xref})")
class _:
    def s_expr(expr, env0, _):
        [var, emu_xref] = expr.children
        env0.assert_expr_is_of_type(var, T_String)
        return (T_Number, env0)

# ==============================================================================
#@ 21.4.4 Properties of the Date Prototype Object

# ==============================================================================
#@ 21.4.4.36 Date.prototype.toISOString

@P('{CONDITION_1} : {var} corresponds with a year that cannot be represented in the {h_emu_xref}')
class _:
    def s_cond(cond, env0, asserting):
        [var, h_emu_xref] = cond.children
        env0.assert_expr_is_of_type(var, T_IntegralNumber_ | T_NaN_Number_)
        return (env0, env0)

@P('{EXPR} : a String representation of {var} in the {h_emu_xref} on the UTC time scale, including all format elements and the UTC offset representation *"Z"*')
class _:
    def s_expr(expr, env0, _):
        [var, h_emu_xref] = expr.children
        env0.assert_expr_is_of_type(var, T_IntegralNumber_ | T_NaN_Number_)
        return (T_String, env0)

# ==============================================================================
#@ 21.4.4.41.2 DateString

@P("{EXPR} : the Name of the entry in {h_emu_xref} with the Number {PP_NAMED_OPERATION_INVOCATION}")
class _:
    def s_expr(expr, env0, _):
        [emu_xref, noi] = expr.children
        env1 = env0.ensure_expr_is_of_type(noi, T_IntegralNumber_)
        return (T_String, env1)

# ==============================================================================
#@ 21.4.4.41.3 TimeZoneString

@P("{EXPR} : an implementation-defined string that is either {EX} or {EXPR}")
class _:
    def s_expr(expr, env0, _):
        [exa, exb] = expr.children
        env0.assert_expr_is_of_type(exa, T_String)
        env0.assert_expr_is_of_type(exb, T_String)
        return (T_String, env0)

@P("{EX} : an implementation-defined timezone name")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_String, env0)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 22 Text Processing

# ==============================================================================
#@ 22.1 String Objects

declare_isom(T_String_exotic_object_, 'must have', 'slot', '[[StringData]]', T_String)

#@ 22.1.3.28 String.prototype.toLowerCase
@P("{EXPR} : the result of toLowercase({var}), according to the Unicode Default Case Conversion algorithm")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_Unicode_code_points_)
        return (T_Unicode_code_points_, env0)

# ==============================================================================
#@ 22.2 RegExp (Regular Expression) Objects

# ==============================================================================
#@ 22.2.1.6 Static Semantics: CharacterValue

@P("{EXPR} : the numeric value according to {h_emu_xref}")
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

@P("{VAL_DESC} : a character")
@P("{LIST_ELEMENTS_DESCRIPTION} : characters")
class _:
    s_tb = T_character_

@P("{EXPR} : the character matched by {PROD_REF}")
class _:
    def s_expr(expr, env0, _):
        [prod_ref] = expr.children
        env0.assert_expr_is_of_type(prod_ref, T_Parse_Node)
        return (T_character_, env0)

@P("{EXPR} : the character whose character value is {var}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_MathInteger_)
        return (T_character_, env1)

@P("{EXPR} : the result of applying that mapping to {var}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_character_)
        return (T_character_, env1)

@P("{EX} : the character {SETTABLE}")
class _:
    def s_expr(expr, env0, _):
        [settable] = expr.children
        env1 = env0.ensure_expr_is_of_type(settable, T_character_)
        return (T_character_, env1)

@P("{EXPR} : the character value of character {var}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_character_)
        return (T_MathInteger_, env0)

@P("{VAL_DESC} : a sequence of characters")
class _:
    s_tb = ListType(T_character_)

@P("{EXPR} : an empty sequence of characters")
@P("{EX} : the empty sequence of characters")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (ListType(T_character_), env0)

@P("{EXPR} : the concatenation of {var} and {var}")
class _:
    def s_expr(expr, env0, _):
        [vara, varb] = expr.children
        env0.assert_expr_is_of_type(vara, ListType(T_character_))
        env0.assert_expr_is_of_type(varb, ListType(T_character_))
        return (ListType(T_character_), env0)

# ==============================================================================
#@ 22.2.2.1 Notation

# ------------------------------------------------------------------------------
# CharSetElement

@P("{EX} : the last code point of {var}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_CharSetElement)
        return (T_code_point_, env0)

@P("{EACH_THING} : code point {DEFVAR} in {var}, iterating backwards from its second-to-last code point")
class _:
    def s_nv(each_thing, env0):
        [loop_var, collection_var] = each_thing.children
        env0.assert_expr_is_of_type(collection_var, T_CharSetElement)
        return env0.plus_new_entry(loop_var, T_code_point_)

@P("{EACH_THING} : single code point {DEFVAR} in {var}")
class _:
    def s_nv(each_thing, env0):
        [loop_var, collection_var] = each_thing.children
        env0.assert_expr_is_of_type(collection_var, T_CharSetElement)
        return env0.plus_new_entry(loop_var, T_code_point_)

# ------------------------------------------------------------------------------
# CharSet
@P("{VAL_DESC} : a CharSet")
class _:
    s_tb = T_CharSet

@P("{COMMAND} : Remove from {var} all characters corresponding to a code point on the right-hand side of the {nonterminal} production.")
class _:
    def s_nv(anode, env0):
        [var, nont] = anode.children
        env0.assert_expr_is_of_type(var, T_CharSet)
        return env0

@P("{CONDITION_1} : {EX} contains only single code points")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_CharSet)
        return (env0, env0)

@P("{CONDITION_1} : {var} does not contain exactly one character")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env1 = env0.ensure_expr_is_of_type(var, T_CharSet)
        return (env1, env1)

@P("{CONDITION_1} : Every CharSetElement of {var} consists of a single character")
class _:
    def s_cond(cond, env0, asserting):
        [ex] = cond.children
        env1 = env0.ensure_expr_is_of_type(ex, T_CharSet)
        return (env1, env1)

@P("{CONDITION_1} : every CharSetElement of {var} consists of a single character (including if {var} is empty)")
class _:
    def s_cond(cond, env0, asserting):
        [exa, exb] = cond.children
        assert exa.source_text() == exb.source_text()
        env1 = env0.ensure_expr_is_of_type(exa, T_CharSet)
        return (env1, env1)

@P("{CONDITION_1} : {var} and {var} each contain exactly one character")
class _:
    def s_cond(cond, env0, asserting):
        [a,b] = cond.children
        env0.assert_expr_is_of_type(a, T_CharSet)
        env0.assert_expr_is_of_type(b, T_CharSet)
        return (env0, env0)

@P("{CONDITION_1} : there exists a CharSetElement in {var} containing exactly one character {DEFVAR} such that {CONDITION_1}")
class _:
    def s_cond(cond, env0, asserting):
        [set_var, char_var, stcond] = cond.children
        env0.assert_expr_is_of_type(set_var, T_CharSet)
        env1 = env0.plus_new_entry(char_var, T_character_)
        return tc_cond(stcond, env1)

# ----

@P("{EXPR} : the one character in CharSet {var}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_CharSet)
        return (T_character_, env1)

@P("{EXPR} : the sequence of characters that is the single CharSetElement of {var}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_CharSet)
        return (ListType(T_character_), env1)

@P("{EXPR} : a new empty CharSet")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_CharSet, env0)

@P("{EXPR} : the CharSet containing all code point values")
@P("{EXPR} : the CharSet containing all code unit values")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_CharSet, env0)

@P("{EXPR} : the CharSet containing all characters with a character value in the inclusive interval from {var} to {var}")
class _:
    def s_expr(expr, env0, _):
        [var1, var2] = expr.children
        env1 = env0.ensure_expr_is_of_type(var1, T_MathInteger_)
        env2 = env0.ensure_expr_is_of_type(var2, T_MathInteger_)
        assert env1 is env0
        assert env2 is env0
        return (T_CharSet, env0)

@P("{EXPR} : the CharSet containing the one string {var}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.ensure_expr_is_of_type(var, ListType(T_character_))
        return (T_CharSet, env0)

@P("{EXPR} : the CharSet containing the single character {code_point_lit}")
@P("{EXPR} : the CharSet containing the single character {var}")
class _:
    def s_expr(expr, env0, _):
        [ex] = expr.children
        env0.ensure_expr_is_of_type(ex, T_character_)
        return (T_CharSet, env0)

@P("{EXPR} : the CharSet containing the character matched by {PROD_REF}")
class _:
    def s_expr(expr, env0, _):
        [prod_ref] = expr.children
        env0.assert_expr_is_of_type(prod_ref, T_Parse_Node)
        return (T_CharSet, env0)

@P("{EXPR} : a one-element CharSet containing {EX}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_character_)
        return (T_CharSet, env0)

@P("{EXPR} : the intersection of CharSets {var} and {var}")
class _:
    def s_expr(expr, env0, _):
        [va, vb] = expr.children
        env0.assert_expr_is_of_type(va, T_CharSet)
        env0.assert_expr_is_of_type(vb, T_CharSet)
        return (T_CharSet, env0)

@P("{EXPR} : the union of CharSets {var}, {var} and {var}")
class _:
    def s_expr(expr, env0, _):
        [va, vb, vc] = expr.children
        enva = env0.ensure_expr_is_of_type(va, T_CharSet)
        envb = env0.ensure_expr_is_of_type(vb, T_CharSet)
        envc = env0.ensure_expr_is_of_type(vc, T_CharSet)
        return (T_CharSet, envs_or([enva, envb, envc]))

@P("{EXPR} : the union of {var} and {var}")
@P("{EXPR} : the union of CharSets {var} and {var}")
class _:
    def s_expr(expr, env0, _):
        [va, vb] = expr.children
        enva = env0.ensure_expr_is_of_type(va, T_CharSet)
        envb = env0.ensure_expr_is_of_type(vb, T_CharSet)
        return (T_CharSet, env_or(enva, envb))

@P("{EXPR} : the ten-element CharSet containing the characters `0`, `1`, `2`, `3`, `4`, `5`, `6`, `7`, `8`, and `9`")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_CharSet, env0)

@P("{EXPR} : the CharSet containing every character in {STR_LITERAL}")
class _:
    def s_expr(expr, env0, _):
        [strlit] = expr.children
        return (T_CharSet, env0)

@P("{EXPR} : the CharSet containing all characters corresponding to a code point on the right-hand side of the {nonterminal} or {nonterminal} productions")
class _:
    def s_expr(expr, env0, _):
        [nont1, nont2] = expr.children
        return (T_CharSet, env0)

@P("{EXPR} : the empty CharSet")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_CharSet, env0)

@P("{EXPR} : the CharSet containing all Unicode code points {DEFVAR} that do not have a {h_a} mapping (that is, scf({var})={var})")
class _:
    def s_expr(expr, env0, _):
        [defvar, h_a, var1, var2] = expr.children
        assert defvar.source_text() == var1.source_text() == var2.source_text()
        return (T_CharSet, env0)

@P("{EXPR} : the CharSet containing all Unicode code points whose character database definition includes the property {var} with value {var}")
class _:
    def s_expr(expr, env0, _):
        [va, vb] = expr.children
        env0.assert_expr_is_of_type(va, ListType(T_code_point_))
        env0.assert_expr_is_of_type(vb, ListType(T_code_point_))
        return (T_CharSet, env0)

@P("{EXPR} : the CharSet containing all Unicode code points whose character database definition includes the property “General_Category” with value {var}")
class _:
    def s_expr(expr, env0, _):
        [v] = expr.children
        env0.assert_expr_is_of_type(v, ListType(T_code_point_))
        return (T_CharSet, env0)

@P("{EXPR} : the CharSet containing all CharSetElements whose character database definition includes the property {var} with value “True”")
class _:
    def s_expr(expr, env0, _):
        [v] = expr.children
        env0.assert_expr_is_of_type(v, ListType(T_code_point_))
        return (T_CharSet, env0)

@P("{EXPR} : the CharSet containing all characters {DEFVAR} such that {var} is not in {var} but {NAMED_OPERATION_INVOCATION} is in {var}")
class _:
    def s_expr(expr, env0, _):
        [loop_var, loop_var2, cs_var, noi, cs_var2] = expr.children
        assert loop_var.source_text() == loop_var2.source_text()
        assert cs_var.source_text() == cs_var2.source_text()
        env0.assert_expr_is_of_type(cs_var, T_CharSet)
        env1 = env0.plus_new_entry(loop_var, T_character_)
        env1.assert_expr_is_of_type(noi, T_character_)
        return (T_CharSet, env0)

@P("{EXPR} : the CharSet containing every CharSetElement of {var} that consists of a single character")
class _:
    def s_expr(expr, env0, _):
        [ex] = expr.children
        env0.assert_expr_is_of_type(ex, T_CharSet)
        return (T_CharSet, env0)

@P("{EXPR} : the CharSet containing the CharSetElements of {var} which are not also CharSetElements of {var}")
class _:
    def s_expr(expr, env0, _):
        [charset_var_a, charset_var_b] = expr.children
        env0.assert_expr_is_of_type(charset_var_a, T_CharSet)
        env0.assert_expr_is_of_type(charset_var_b, T_CharSet)
        return (T_CharSet, env0)

@P("{NAMED_OPERATION_INVOCATION} : the CharSet returned by {h_emu_grammar}")
class _:
    def s_expr(expr, env0, _):
        [emu_grammar] = expr.children
        return (T_CharSet, env0)

# ---

@P("{EACH_THING} : CharSetElement {DEFVAR} in {var} containing more than 1 character, iterating in descending order of length")
class _:
    def s_nv(each_thing, env0):
        [loop_var, collection_var] = each_thing.children
        env0.assert_expr_is_of_type(collection_var, T_CharSet)
        return env0.plus_new_entry(loop_var, T_CharSetElement)

# ------------------------------------------------------------------------------
# MatchState

@P("{VAL_DESC} : a MatchState")
class _:
    s_tb = T_MatchState

# ------------------------------------------------------------------------------

@P("{VAL_DESC} : a MatchResult")
class _:
    s_tb = T_MatchResult

@P("{VAL_DESC} : a MatcherContinuation")
class _:
    s_tb = T_MatcherContinuation

@P("{VAL_DESC} : a Matcher")
class _:
    s_tb = T_Matcher

# ==============================================================================
#@ 22.2.2.1.1 RegExp Records

@P("{VAL_DESC} : a RegExp Record")
class _:
    s_tb = T_RegExp_Record

# ==============================================================================
#@ 22.2.2.2 Runtime Semantics: CompilePattern

@P("{VAL_DESC} : an Abstract Closure that takes {VAL_DESC} and {VAL_DESC} and returns {VAL_DESC}")
class _:
    def s_tb(val_desc, env):
        assert val_desc.source_text() == 'an Abstract Closure that takes a List of characters and a non-negative integer and returns a MatchResult'
        return T_RegExpMatcher_

# ==============================================================================
#@ 22.2.2.4 Runtime Semantics: CompileAssertion

@P("{CONDITION_1} : the character {EX} is matched by {nonterminal}")
class _:
    def s_cond(cond, env0, asserting):
        [ex, nonterminal] = cond.children
        env0.assert_expr_is_of_type(ex, T_character_)
        assert nonterminal.source_text() == '|LineTerminator|'
        return (env0, env0)

# ==============================================================================
#@ 22.2.2.7 Runtime Semantics: CompileAtom

@P("{EXPR} : an empty List of Matchers")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (ListType(T_Matcher), env0)

@P("{EXPR} : the last Matcher in {var}")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, ListType(T_Matcher))
        return (T_Matcher, env0)

# ==============================================================================
#@ 22.2.2.7.3 Canonicalize

@P("{CONDITION_1} : the file {h_a} of the Unicode Character Database provides a simple or common case folding mapping for {var}")
class _:
    def s_cond(cond, env0, asserting):
        [h_a, var] = cond.children
        assert h_a.source_text() == '<a href="https://unicode.org/Public/UCD/latest/ucd/CaseFolding.txt"><code>CaseFolding.txt</code></a>'
        env1 = env0.ensure_expr_is_of_type(var, T_character_)
        return (env1, env1)

@P("{EXPR} : the result of toUppercase(« {var} »), according to the Unicode Default Case Conversion algorithm")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_code_point_)
        return (T_Unicode_code_points_, env0)

# ==============================================================================
#@ 22.2.2.9.7 UnicodeMatchProperty

# Unicode property {name, alias, value, value alias}
@P("{VAL_DESC} : a Unicode property name or property alias listed in the “Property name and aliases” column of {h_emu_xref}")
@P("{VAL_DESC} : a Unicode {h_emu_not_ref_property_name} listed in the \u201c{h_emu_not_ref_Property_name}\u201d column of {h_emu_xref}")
class _:
    s_tb = a_subset_of(T_Unicode_code_points_)

@P("{VAL_DESC} : a Unicode property name")
class _:
    s_tb = a_subset_of(T_Unicode_code_points_)

@P("{VAL_DESC} : a Unicode property value or property value alias for the General_Category (gc) property listed in {h_a}")
class _:
    s_tb = a_subset_of(T_Unicode_code_points_)

@P("{VAL_DESC} : a Unicode property value")
class _:
    s_tb = a_subset_of(T_Unicode_code_points_)

@P("{VAL_DESC} : a Unicode {h_emu_not_ref_property_name} or property alias listed in the “{h_emu_not_ref_Property_name} and aliases” column of {h_emu_xref} or {h_emu_xref}")
class _:
    s_tb = a_subset_of(T_Unicode_code_points_)

@P("{VAL_DESC} : a binary Unicode property or binary property alias listed in the “{h_emu_not_ref_Property_name} and aliases” column of {h_emu_xref}, or a binary Unicode property of strings listed in the “{h_emu_not_ref_Property_name}” column of {h_emu_xref}")
@P("{VAL_DESC} : a binary property of strings listed in the “Property name” column of {h_emu_xref}")
class _:
    s_tb = a_subset_of(T_Unicode_code_points_)

@P("{VAL_DESC} : a canonical, unaliased Unicode property name listed in the “Canonical property name” column of {h_emu_xref}")
class _:
    s_tb = a_subset_of(T_Unicode_code_points_)

@P("{VAL_DESC} : a property value or property value alias for the Unicode property {var} listed in {h_a}")
class _:
    def s_tb(val_desc, env):
        [var, h_a] = val_desc.children
        env.assert_expr_is_of_type(var, T_Unicode_code_points_)
        return T_Unicode_code_points_

@P("{EXPR} : the canonical {h_emu_not_ref_property_name} of {var} as given in the “Canonical {h_emu_not_ref_property_name}” column of the corresponding row")
class _:
    def s_expr(expr, env0, _):
        [_, v, _] = expr.children
        env0.assert_expr_is_of_type(v, ListType(T_code_point_))
        return (ListType(T_code_point_), env0)

@P("{CONDITION_1} : the source text matched by {PROD_REF} is not a Unicode property value or property value alias for the General_Category (gc) property listed in {h_a}, nor a binary property or binary property alias listed in the “Property name and aliases” column of {h_emu_xref}, nor a binary property of strings listed in the “Property name” column of {h_emu_xref}")
class _:
    def s_cond(cond, env0, asserting):
        [prod_ref, h_a, h_emu_xref1, h_emu_xref2] = cond.children
        env0.assert_expr_is_of_type(prod_ref, T_Parse_Node)
        return (env0, env0)

@P("{CONDITION_1} : the source text matched by {PROD_REF} is not a property value or property value alias for the Unicode property or property alias given by the source text matched by {PROD_REF} listed in {h_a}")
class _:
    def s_cond(cond, env0, asserting):
        [prod_refa, prod_refb, h_a] = cond.children
        env0.assert_expr_is_of_type(prod_refa, T_Parse_Node)
        env0.assert_expr_is_of_type(prod_refb, T_Parse_Node)
        return (env0, env0)

# ==============================================================================
#@ 22.2.2.9.8 UnicodeMatchPropertyValue

@P("{EXPR} : the canonical property value of {var} as given in the “Canonical property value” column of the corresponding row")
class _:
    def s_expr(expr, env0, _):
        [v] = expr.children
        env0.assert_expr_is_of_type(v, ListType(T_code_point_))
        return (ListType(T_code_point_), env0)

# ==============================================================================
#@ 22.2.3 Abstract Operations for RegExp Creation

declare_isom(T_Object, 'might have', 'slot', '[[OriginalSource]]', T_String)
declare_isom(T_Object, 'might have', 'slot', '[[OriginalFlags]]',  T_String)
declare_isom(T_Object, 'might have', 'slot', '[[RegExpRecord]]',   T_RegExp_Record)
declare_isom(T_Object, 'might have', 'slot', '[[RegExpMatcher]]',  T_RegExpMatcher_)

# ==============================================================================
#@ 22.2.6.13.1 EscapeRegExpPattern

@P("{EXPR} : a String in the form of a {var} equivalent to {var} interpreted as UTF-16 encoded Unicode code points ({h_emu_xref}), in which certain code points are escaped as described below. {var} may or may not differ from {var}; however, the Abstract Closure that would result from evaluating {var} as a {var} must behave identically to the Abstract Closure given by the constructed object's {DSBN} internal slot. Multiple calls to this abstract operation using the same values for {var} and {var} must produce identical results")
class _:
    def s_expr(expr, env0, _):
        # XXX
        return (T_String, env0)

@P("{COMMAND} : The code points `/` or any {nonterminal} occurring in the pattern shall be escaped in {var} as necessary to ensure that the string-concatenation of {EX}, {EX}, {EX}, and {EX} can be parsed (in an appropriate lexical context) as a {nonterminal} that behaves identically to the constructed regular expression. For example, if {var} is {STR_LITERAL}, then {var} could be {STR_LITERAL} or {STR_LITERAL}, among other possibilities, but not {STR_LITERAL}, because `///` followed by {var} would be parsed as a {nonterminal} rather than a {nonterminal}. If {var} is the empty String, this specification can be met by letting {var} be {STR_LITERAL}.")
class _:
    def s_nv(anode, env0):
        # XXX
        return env0

# ==============================================================================
#@ 22.2.7.2 RegExpBuiltinExec

@P("{VAL_DESC} : an initialized RegExp instance")
class _:
    s_tb = a_subset_of(T_Object)

@P("{EXPR} : the index into {var} of the character that was obtained from element {EX} of {var}")
class _:
    def s_expr(expr, env0, _):
        [list_var, index_var, str_var] = expr.children
        env0.assert_expr_is_of_type(list_var, T_List)
        env0.assert_expr_is_of_type(index_var, T_MathInteger_)
        env0.assert_expr_is_of_type(str_var, T_String) # todo: element of String
        return (T_MathInteger_, env0)

@P("{CONDITION_1} : {EX} contains any {nonterminal}")
class _:
    def s_cond(cond, env0, asserting):
        [rvar, nonterminal] = cond.children
        env0.assert_expr_is_of_type(rvar, T_Object)
        return (env0, env0)

@P("{CONDITION_1} : the {var}<sup>th</sup> capture of {var} was defined with a {nonterminal}")
class _:
    def s_cond(cond, env0, asserting):
        [ivar, rvar, nonterminal] = cond.children
        env0.assert_expr_is_of_type(ivar, T_MathInteger_)
        env0.assert_expr_is_of_type(rvar, T_Object)
        return (env0, env0)

@P("{PROD_REF} : that {nonterminal}")
class _:
    def s_expr(expr, env0, _):
        [nont] = expr.children
        return (ptn_type_for(nont), env0)

# ==============================================================================
#@ 22.2.7.5 Match Records

@P("{VAL_DESC} : a Match Record")
class _:
    s_tb = T_Match_Record

@P("{LIST_ELEMENTS_DESCRIPTION} : either Match Records or *undefined*")
class _:
    s_tb = T_Match_Record | T_Undefined

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 23 Indexed Collections

# ==============================================================================
#@ 23.1.3.30.1 SortIndexedProperties

@P("{COMMAND} : Sort {var} using an implementation-defined sequence of {h_emu_meta_start}calls to {var}{h_emu_meta_end}. If any such call returns an abrupt completion, stop before performing any further calls to {var} and return that Completion Record.")
class _:
    def s_nv(anode, env0):
        [var, _, comparator, _, comparator] = anode.children
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_Tangible_))
        return env1

# ==============================================================================
#@ 23.2 TypedArray Objects

@P("{VAL_DESC} : a TypedArray")
class _:
    s_tb = T_TypedArray_object_

@P("{VAL_DESC} : a TypedArray element type")
class _:
    s_tb = T_TypedArray_element_type

@P("{VAL_DESC} : a String which is the name of a TypedArray constructor in {h_emu_xref}")
class _:
    s_tb = a_subset_of(T_String)

@P("{EXPR} : the intrinsic object associated with the constructor name {DOTTING} in {h_emu_xref}")
class _:
    def s_expr(expr, env0, _):
        [dotting, emu_xref] = expr.children
        env0.assert_expr_is_of_type(dotting, T_String)
        return (T_function_object_, env0)

@P("{EXPR} : the String value of the Constructor Name value specified in {h_emu_xref} for this <var>TypedArray</var> constructor")
class _:
    def s_expr(expr, env0, _):
        [emu_xref] = expr.children
        return (T_String, env0)

@P("{EXPR} : the abstract operation named in the Conversion Operation column in {h_emu_xref} for Element Type {var}")
class _:
    def s_expr(expr, env0, _):
        [emu_xref, var] = expr.children
        env1 = env0.ensure_expr_is_of_type(var, T_TypedArray_element_type)
        return (ProcType((T_Tangible_,), T_IntegralNumber_), env1)

@P("{EXPR} : the Element Type value specified in {h_emu_xref} for {EX}")
class _:
    def s_expr(expr, env0, _):
        [emu_xref, ex] = expr.children
        env1 = env0.ensure_expr_is_of_type(ex, T_String)
        return (T_TypedArray_element_type, env0)

@P("{EXPR} : the Element Size value specified in {h_emu_xref} for Element Type {var}")
class _:
    def s_expr(expr, env0, _):
        [emu_xref, var] = expr.children
        assert var.source_text() in ['_type_', '_srcType_', '_elementType_']
        env1 = env0.ensure_expr_is_of_type(var, T_TypedArray_element_type)
        return (T_MathInteger_, env1)

@P("{EXPR} : the Element Size value specified in {h_emu_xref} for {EX}")
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
declare_isom(T_Object, 'might have', 'slot', '[[MapData]]', ListType(T_MapData_record_))

# 24.2 Set Objects
declare_isom(T_Object, 'might have', 'slot', '[[SetData]]', ListType(T_Tangible_ | T_tilde_empty_))

# 24.3 WeakMap Objects
declare_isom(T_WeakMap_object_, 'must have', 'slot', '[[WeakMapData]]', ListType(T_MapData_record_))

# 24.4 WeakSet Objects
declare_isom(T_WeakSet_object_, 'must have', 'slot', '[[WeakSetData]]', ListType(T_Tangible_ | T_tilde_empty_))

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 25 Structured Data

# ==============================================================================
#@ 25.1 ArrayBuffer Objects

@P("{VAL_DESC} : a read-modify-write modification function")
class _:
    s_tb = T_ReadModifyWrite_modification_closure

@P("{VAL_DESC} : an ArrayBuffer")
class _:
    s_tb = T_ArrayBuffer_object_

@P("{VAL_DESC} : an ArrayBuffer or SharedArrayBuffer")
class _:
    s_tb = T_ArrayBuffer_object_ | T_SharedArrayBuffer_object_

# 25.1.2.1 AllocateArrayBuffer
# 25.1.6   Properties of ArrayBuffer Instances

declare_isom(T_ArrayBuffer_object_, 'must have',  'slot', '[[ArrayBufferData]]',          T_Data_Block | T_Null)
declare_isom(T_ArrayBuffer_object_, 'must have',  'slot', '[[ArrayBufferByteLength]]',    T_MathNonNegativeInteger_)
declare_isom(T_ArrayBuffer_object_, 'must have',  'slot', '[[ArrayBufferDetachKey]]',     T_Undefined | T_host_defined_)
declare_isom(T_ArrayBuffer_object_, 'might have', 'slot', '[[ArrayBufferMaxByteLength]]', T_MathNonNegativeInteger_)

# 25.1.2.*
@P("{CONDITION_1} : There are sufficient bytes in {var} starting at {var} to represent a value of {var}")
class _:
    def s_cond(cond, env0, asserting):
        [ab_var, st_var, t_var] = cond.children
        env0.assert_expr_is_of_type(ab_var, T_ArrayBuffer_object_ | T_SharedArrayBuffer_object_)
        env0.assert_expr_is_of_type(st_var, T_MathInteger_)
        env0.assert_expr_is_of_type(t_var, T_TypedArray_element_type)
        return (env0, env0)

@P("{EX} : a nondeterministically chosen byte value")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_MathNonNegativeInteger_, env0)

@P("{EXPR} : a List of length {var} whose elements are nondeterministically chosen byte values")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        env0.assert_expr_is_of_type(var, T_MathInteger_)
        return (ListType(T_MathInteger_), env0)

@P("{LIST_ELEMENTS_DESCRIPTION} : byte values")
class _:
    s_tb = a_subset_of(T_MathInteger_)

# ==============================================================================
#@ 25.2 SharedArrayBuffer Objects

@P("{VAL_DESC} : a SharedArrayBuffer")
class _:
    s_tb = T_SharedArrayBuffer_object_

# 25.2.1.1 AllocateSharedArrayBuffer
# 25.2.5   Properties of SharedArrayBuffer Instances

declare_isom(T_SharedArrayBuffer_object_, 'must have',  'slot', '[[ArrayBufferData]]',           T_Shared_Data_Block)
declare_isom(T_SharedArrayBuffer_object_, 'might have', 'slot', '[[ArrayBufferByteLength]]',     T_MathNonNegativeInteger_)
declare_isom(T_SharedArrayBuffer_object_, 'might have', 'slot', '[[ArrayBufferByteLengthData]]', T_Shared_Data_Block)
declare_isom(T_SharedArrayBuffer_object_, 'might have', 'slot', '[[ArrayBufferMaxByteLength]]',  T_MathNonNegativeInteger_)

# ==============================================================================
#@ 25.3 DataView Objects

@P("{VAL_DESC} : a DataView")
class _:
    s_tb = T_DataView_object_

# ==============================================================================
#@ 25.3.1.1 DataView With Buffer Witness Records

@P("{VAL_DESC} : a DataView With Buffer Witness Record")
class _:
    s_tb = T_DataView_With_Buffer_Witness_Record

# ==============================================================================
#@ 25.3.5 Properties of DataView Instances

#> DataView instances each have
#> [[DataView]], [[ViewedArrayBuffer]], [[ByteLength]], and [[ByteOffset]]
#> internal slots.

declare_isom(T_DataView_object_, 'must have', 'slot', '[[DataView]]',          T_tilde_unused_)
declare_isom(T_DataView_object_, 'must have', 'slot', '[[ViewedArrayBuffer]]', T_ArrayBuffer_object_ | T_SharedArrayBuffer_object_)
declare_isom(T_DataView_object_, 'must have', 'slot', '[[ByteLength]]',        T_MathNonNegativeInteger_ | T_tilde_auto_)
declare_isom(T_DataView_object_, 'must have', 'slot', '[[ByteOffset]]',        T_MathNonNegativeInteger_)

# ==============================================================================
#@ 25.4.1 Waiter Record

@P("{VAL_DESC} : a Waiter Record")
@P("{LIST_ELEMENTS_DESCRIPTION} : Waiter Records")
class _:
    s_tb = T_Waiter_Record

@P("{CONDITION_1} : There is no Waiter Record in {DOTTING} whose {dsb_word} field is {EX} and whose {dsb_word} field is {EX}")
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

@P("{VAL_DESC} : a WaiterList Record")
class _:
    s_tb = T_WaiterList_Record

#> The agent cluster has a store of WaiterList Records;
#> the store is indexed by (_block_, _i_), where
#> _block_ is a Shared Data Block and _i_ a byte offset into the memory of _block_.
#> WaiterList Records are agent-independent:
#> a lookup in the store of WaiterList Records by (_block_, _i_)
#> will result in the same WaiterList object in any agent in the agent cluster.

@P("{EXPR} : the WaiterList Record that is referenced by the pair ({var}, {var})")
class _:
    def s_expr(expr, env0, _):
        [sdb, i] = expr.children
        env0.assert_expr_is_of_type(sdb, T_Shared_Data_Block)
        env0.assert_expr_is_of_type(i, T_MathInteger_)
        return (T_WaiterList_Record, env0)

#> Each WaiterList Record has a <dfn>critical section</dfn> ...

@P("{COMMAND} : Wait until no agent is in the critical section for {var}, then enter the critical section for {var} (without allowing any other agent to enter).")
class _:
    def s_nv(anode, env0):
        [var1, var2] = anode.children
        [var_name1] = var1.children
        [var_name2] = var2.children
        assert var_name1 == var_name2
        env1 = env0.ensure_expr_is_of_type(var1, T_WaiterList_Record)
        return env1

@P("{COMMAND} : Leave the critical section for {var}.")
class _:
    def s_nv(anode, env0):
        [var] = anode.children
        env0.assert_expr_is_of_type(var, T_WaiterList_Record)
        return env0

@P("{CONDITION_1} : The surrounding agent is in the critical section for {var}")
class _:
    def s_cond(cond, env0, asserting):
        [var] = cond.children
        env0.assert_expr_is_of_type(var, T_WaiterList_Record)
        return (env0, env0)

@P("{CONDITION_1} : The surrounding agent is not in the critical section for any WaiterList Record")
class _:
    def s_cond(cond, env0, asserting):
        # nothing to check
        return (env0, env0)

# ==============================================================================
#@ 25.4.3.11 SuspendThisAgent

@P("{EXPR} : an implementation-defined non-negative mathematical value")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_MathReal_, env0)

@P("{COMMAND} : Perform {PP_NAMED_OPERATION_INVOCATION} and suspend the surrounding agent until the time is {DOTTING}, performing the combined operation in such a way that a notification that arrives after the critical section is exited but before the suspension takes effect is not lost. The surrounding agent can only wake from suspension due to a timeout or due to another agent calling NotifyWaiter with arguments {var} and {var} (i.e. via a call to `Atomics.notify`).")
class _:
    def s_nv(anode, env0):
        [noi, t_var, *blah] = anode.children
        env0.assert_expr_is_of_type(noi, T_tilde_unused_)
        env0.assert_expr_is_of_type(t_var, T_MathReal_ | T_MathPosInfinity_)
        return env0

# ==============================================================================
#@ 25.4.3.12 NotifyWaiter

@P("{COMMAND} : Wake the agent whose signifier is {DOTTING} from suspension.")
class _:
    def s_nv(anode, env0):
        [var] = anode.children
        env0.assert_expr_is_of_type(var, T_agent_signifier_)
        return env0

# ==============================================================================
#@ 25.5.1 JSON.parse

@P("{COMMAND} : Parse {PP_NAMED_OPERATION_INVOCATION} as a JSON text as specified in ECMA-404. Throw a {ERROR_TYPE} exception if it is not a valid JSON text as defined in that specification.")
class _:
    def s_nv(anode, env0):
        [noi, error_type] = anode.children
        env0.assert_expr_is_of_type(noi, T_Unicode_code_points_)
        return env0

@P("{CONDITION_1} : {PROD_REF} is contained within a {nonterminal} that is being parsed for JSON.parse (see step {h_emu_xref} of {h_emu_xref})")
@P("{CONDITION_1} : {PROD_REF} is contained within a {nonterminal} that is being evaluated for JSON.parse (see step {h_emu_xref} of {h_emu_xref})")
class _:
    def s_cond(cond, env0, asserting):
        [prod_ref, nont, step_xref, alg_xref] = cond.children
        env0.assert_expr_is_of_type(prod_ref, T_Parse_Node)
        return (env0, env0)

    def d_exec(cond):
        [prod_ref, nont, step_xref, alg_xref] = cond.children
        node = EXEC(prod_ref, ES_ParseNode)
        container_nt = nt_name_from_nonterminal_node(nont)
        assert container_nt == 'Script'
        if node.root().symbol != container_nt: return False
        # TODO: detect whether the Script is being parsed/evaluated for JSON.parse
        return False

@P("{VAL_DESC} : an Object that is defined by either an {nonterminal} or an {nonterminal}")
class _:
    s_tb = a_subset_of(T_Object)

# ==============================================================================
#@ 25.5.2.1 JSON Serialization Record

@P("{VAL_DESC} : a JSON Serialization Record")
class _:
    s_tb = T_JSON_Serialization_Record

# ==============================================================================
#@ 25.5.2.3 QuoteJSONString

@P("{CONDITION_1} : {EX} is listed in the “Code Point” column of {h_emu_xref}")
class _:
    def s_cond(cond, env0, asserting):
        [ex, emu_xref] = cond.children
        env0.assert_expr_is_of_type(ex, T_code_point_)
        return (env0, env0)

@P("{EX} : the escape sequence for {var} as specified in the “Escape Sequence” column of the corresponding row")
class _:
    def s_expr(expr, env0, _):
        [var] = expr.children
        return (T_String, env0)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 26 Managing Memory

# ==============================================================================
#@ 26.1 WeakRef Objects

@P("{VAL_DESC} : a WeakRef")
class _:
    s_tb = T_WeakRef_object_

declare_isom(T_WeakRef_object_, 'must have', 'slot', '[[WeakRefTarget]]', T_Object | T_Symbol | T_tilde_empty_)

# ==============================================================================
#@ 26.2 FinalizationRegistry Objects

@P("{VAL_DESC} : a FinalizationRegistry")
class _:
    s_tb = T_FinalizationRegistry_object_

T_FinalizationRegistryCellRecord_ = RecordType('', (
        ('[[WeakRefTarget]]'  , T_Object | T_Symbol | T_tilde_empty_),
        ('[[HeldValue]]'      , T_Tangible_),
        ('[[UnregisterToken]]', T_Object | T_tilde_empty_),
    )
)

# 26.2.1.1 FinalizationRegistry

declare_isom(T_FinalizationRegistry_object_, 'must have', 'slot', '[[Realm]]', T_Realm_Record)
declare_isom(T_FinalizationRegistry_object_, 'must have', 'slot', '[[CleanupCallback]]', T_JobCallback_Record)
declare_isom(T_FinalizationRegistry_object_, 'must have', 'slot', '[[Cells]]',           ListType(T_FinalizationRegistryCellRecord_))

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 27 Control Abstraction Objects

# ==============================================================================
#@ 27.1 Iteration

@P("{VAL_DESC} : an Iterator")
class _:
    s_tb = T_Iterator_object_

# ==============================================================================
#@ 27.1.1 Common Iteration Interfaces

#> An interface is a set of property keys
#> whose associated values match a specific specification.
#> Any object that provides all the properties
#> as described by an interface's specification
#> <em>conforms</em> to that interface.
#> An interface is not represented by a distinct object.
#> There may be many separately implemented objects that conform to any interface.
#> An individual object may conform to multiple interfaces.

# ==============================================================================
#@ 27.1.1.5 The <i>IteratorResult</i> Interface

@P("{VAL_DESC} : an Object that conforms to the <i>IteratorResult</i> interface")
class _:
    s_tb = a_subset_of(T_Object)

# ==============================================================================
#@ 27.2 Promise Objects

@P("{VAL_DESC} : a Promise")
class _:
    s_tb = T_Promise_object_

#@ 27.2.1.1 PromiseCapability Records

@P("{VAL_DESC} : a PromiseCapability Record for an intrinsic {percent_word}")
class _:
    s_tb = T_PromiseCapability_Record

@P("{VAL_DESC} : a PromiseCapability Record")
class _:
    s_tb = T_PromiseCapability_Record

#@ 27.2.1.1.1 IfAbruptRejectPromise

@P("{COMMAND} : IfAbruptRejectPromise({var}, {var}).")
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

@P("{VAL_DESC} : a PromiseReaction Record")
@P("{LIST_ELEMENTS_DESCRIPTION} : PromiseReaction Records")
class _:
    s_tb = T_PromiseReaction_Record

#@ 27.2.1.3 CreateResolvingFunctions

T_boolean_value_record_ = RecordType('', (('[[Value]]', T_Boolean),))

declare_isom(T_function_object_, 'might have', 'slot', '[[Promise]]',         T_Object)
declare_isom(T_function_object_, 'might have', 'slot', '[[AlreadyResolved]]', T_boolean_value_record_)

#@ 27.2.4 Properties of the Promise Constructor

declare_isom(T_function_object_, 'might have', 'slot', '[[AlreadyCalled]]',     T_boolean_value_record_ | T_Boolean)
declare_isom(T_function_object_, 'might have', 'slot', '[[Index]]',             T_MathNonNegativeInteger_)
declare_isom(T_function_object_, 'might have', 'slot', '[[Values]]',            ListType(T_Tangible_))
declare_isom(T_function_object_, 'might have', 'slot', '[[Errors]]',            ListType(T_Tangible_))
declare_isom(T_function_object_, 'might have', 'slot', '[[Capability]]',        T_PromiseCapability_Record)
declare_isom(T_function_object_, 'might have', 'slot', '[[RemainingElements]]', RecordType('', (('[[Value]]', T_MathInteger_),)))

# ==============================================================================
#@ 27.5 Generator Objects

#> A Generator is an instance of a generator function
#> and conforms to both the <i>Iterator</i> and <i>Iterable</i> interfaces.

@P("{VAL_DESC} : a Generator")
class _:
    s_tb = T_Generator_object_

@P("{CONDITION_1} : the generator either threw an exception or performed either an implicit or explicit return")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

# ==============================================================================
#@ 27.6 AsyncGenerator Objects

@P("{VAL_DESC} : an AsyncGenerator")
class _:
    s_tb = T_AsyncGenerator_object_

@P("{CONDITION_1} : the async generator either threw an exception or performed either an implicit or explicit return")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

@P("{LIST_ELEMENTS_DESCRIPTION} : AsyncGeneratorRequest Records")
class _:
    s_tb = T_AsyncGeneratorRequest_Record

# ==============================================================================
#@ 27.7.5.2 AsyncBlockStart

@P("{CONDITION_1} : the async function either threw an exception or performed an implicit or explicit return; all awaiting is done")
class _:
    def s_cond(cond, env0, asserting):
        [] = cond.children
        return (env0, env0)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 28 Reflection

#@ 28.2.2.1 Proxy.revocable
declare_isom(T_function_object_, 'might have', 'slot', '[[RevocableProxy]]', T_Proxy_exotic_object_ | T_Null)

#@ 28.3 Module Namespace Objects
@P("{VAL_DESC} : a Module Namespace Object")
class _:
    s_tb = T_module_namespace_exotic_object_

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
#@ 29 Memory Model

# ==============================================================================
#@ 29.1 Memory Model Fundamentals

#> A <dfn>Shared Data Block event</dfn> is either
#> a <dfn>ReadSharedMemory</dfn>,
#> <dfn>WriteSharedMemory</dfn>, or
#> <dfn>ReadModifyWriteSharedMemory</dfn> Record.

T_Shared_Data_Block_Event = T_ReadSharedMemory_Event | T_WriteSharedMemory_Event | T_ReadModifyWriteSharedMemory_Event

T_Event = T_Shared_Data_Block_Event | T_Synchronize_Event | T_Host_Specific_Event

@P("{VAL_DESC} : a WriteSharedMemory event")
class _:
    s_tb = T_WriteSharedMemory_Event

@P("{VAL_DESC} : a ReadModifyWriteSharedMemory event")
class _:
    s_tb = T_ReadModifyWriteSharedMemory_Event

@P("{VAL_DESC} : a ReadSharedMemory or ReadModifyWriteSharedMemory event")
class _:
    s_tb = T_ReadSharedMemory_Event | T_ReadModifyWriteSharedMemory_Event

@P("{VAL_DESC} : a ReadSharedMemory, WriteSharedMemory, or ReadModifyWriteSharedMemory event")
@P("{VAL_DESC} : a Shared Data Block event")
class _:
    s_tb = T_Shared_Data_Block_Event

@P("{LIST_ELEMENTS_DESCRIPTION} : events")
class _:
    s_tb = T_Event

@P("{LIST_ELEMENTS_DESCRIPTION} : WriteSharedMemory or ReadModifyWriteSharedMemory events")
@P("{LIST_ELEMENTS_DESCRIPTION} : either WriteSharedMemory or ReadModifyWriteSharedMemory events")
class _:
    s_tb = T_WriteSharedMemory_Event | T_ReadModifyWriteSharedMemory_Event

@P('{CONDITION_1} : {SETTABLE} and {SETTABLE} are not the same Shared Data Block event')
class _:
    def s_cond(cond, env0, asserting):
        return s_X_and_Y_are_the_same_Foo_Record(cond, T_Shared_Data_Block_Event, env0)

@P("{CONDITION_1} : {var} and {var} are both WriteSharedMemory or ReadModifyWriteSharedMemory events")
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

@P("{CONDITION_1} : there exists an event {DEFVAR} such that {CONDITION}")
class _:
    def s_cond(cond, env0, asserting):
        [let_var, stcond] = cond.children
        env_for_cond = env0.plus_new_entry(let_var, T_Shared_Data_Block_Event)
        return tc_cond(stcond, env_for_cond)

# ------------------------------------------------------------------------------
#> A <dfn>Synchronize event</dfn> has no fields,
#> and exists purely to directly constrain the permitted orderings of other events.

@P("{EXPR} : a new Synchronize event")
class _:
    def s_expr(expr, env0, _):
        [] = expr.children
        return (T_Synchronize_Event, env0)

@P("{VAL_DESC} : a Synchronize event")
class _:
    s_tb = T_Synchronize_Event

@P("{LIST_ELEMENTS_DESCRIPTION} : pairs of Synchronize events")
class _:
    s_tb = T_event_pair_

# ------------------------------------------------------------------------------
#> Let the range of
#> a ReadSharedMemory, WriteSharedMemory, or ReadModifyWriteSharedMemory event
#> be the Set of contiguous integers
#> from its [[ByteIndex]] to [[ByteIndex]] + [[ElementSize]] - 1.

@P("{CONDITION_1} : {var} has {var} in its range")
class _:
    def s_cond(cond, env0, asserting):
        [sdbe_var, loc_var] = cond.children
        env1 = env0.ensure_expr_is_of_type(sdbe_var, T_Shared_Data_Block_Event)
        env2 = env1.ensure_expr_is_of_type(loc_var, T_MathInteger_)
        return (env2, env2)

@P("{CONDITION_1} : {var} and {var} do not have disjoint ranges")
@P("{CONDITION_1} : {var} and {var} have equal ranges")
@P("{CONDITION_1} : {var} and {var} have overlapping ranges")
class _:
    def s_cond(cond, env0, asserting):
        [ea, eb] = cond.children
        env0.assert_expr_is_of_type(ea, T_Shared_Data_Block_Event)
        env0.assert_expr_is_of_type(eb, T_Shared_Data_Block_Event)
        return (env0, env0)

@P("{CONDITION_1} : there exists a WriteSharedMemory or ReadModifyWriteSharedMemory event {DEFVAR} that has {var} in its range such that {CONDITION_1}")
class _:
    def s_cond(cond, env0, asserting):
        [let_var, i, stcond] = cond.children
        env0.assert_expr_is_of_type(i, T_MathInteger_)
        env_for_cond = env0.plus_new_entry(let_var, T_WriteSharedMemory_Event | T_ReadModifyWriteSharedMemory_Event)
        return tc_cond(stcond, env_for_cond)

# ==============================================================================
#@ 29.2 Agent Events Records

@P("{LIST_ELEMENTS_DESCRIPTION} : Agent Events Records")
class _:
    s_tb = T_Agent_Events_Record

@P("{EXPR} : the Agent Events Record of {DOTTING} whose {DSBN} is {PP_NAMED_OPERATION_INVOCATION}")
class _:
    def s_expr(expr, env0, _):
        [dotting, dsbn, e] = expr.children
        env0.assert_expr_is_of_type(dotting, ListType(T_Agent_Events_Record))
        assert dsbn.source_text() == '[[AgentSignifier]]'
        env0.assert_expr_is_of_type(e, T_agent_signifier_)
        return (T_Agent_Events_Record, env0)

# ==============================================================================
#@ 29.3 Chosen Value Records

@P("{LIST_ELEMENTS_DESCRIPTION} : Chosen Value Records")
class _:
    s_tb = T_Chosen_Value_Record

# ==============================================================================
#@ 29.4 Candidate Executions

@P("{VAL_DESC} : a candidate execution")
@P("{VAL_DESC} : a candidate execution Record")
class _:
    s_tb = T_Candidate_Execution_Record

# ==============================================================================
#@ 29.5 Abstract Operations for the Memory Model

@P("{VAL_DESC} : a Set of events")
class _:
    s_tb = T_Set

# ==============================================================================
#@ 29.6 Relations of Candidate Executions

#@ 29.6.1 agent-order
@P("{VAL_DESC} : an agent-order Relation")
class _:
    s_tb = T_Relation

#@ 29.6.2 reads-bytes-from
@P("{VAL_DESC} : a reads-bytes-from mathematical function")
class _:
    s_tb = ProcType((T_Event,), ListType(T_WriteSharedMemory_Event | T_ReadModifyWriteSharedMemory_Event))

#@ 29.6.3 reads-from
@P("{VAL_DESC} : a reads-from Relation")
class _:
    s_tb = T_Relation

#@ 29.6.4 host-synchronizes-with
@P("{VAL_DESC} : a host-synchronizes-with Relation")
class _:
    s_tb = T_Relation

#@ 29.6.5 synchronizes-with
@P("{VAL_DESC} : a synchronizes-with Relation")
class _:
    s_tb = T_Relation

#@ 29.6.6 happens-before
@P("{VAL_DESC} : a happens-before Relation")
class _:
    s_tb = T_Relation

# ==============================================================================
#@ 29.8 Races

@P("{CONDITION_1} : {var} and {var} are in a race in {var}")
class _:
    def s_cond(cond, env0, asserting):
        [ea, eb, exe] = cond.children
        env0.assert_expr_is_of_type(ea, T_Shared_Data_Block_Event)
        env0.assert_expr_is_of_type(eb, T_Shared_Data_Block_Event)
        env0.assert_expr_is_of_type(exe, T_Candidate_Execution_Record)
        return (env0, env0)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

# vim: sw=4 ts=4 expandtab
