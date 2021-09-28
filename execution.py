# ecmaspeak-py/execution.py
# Executing ecmaspeak pseudocode.
#
# Copyright (C) 2021  J. Michael Dyck <jmdyck@ibiblio.org>

import sys, pdb, re
from pprint import pprint
import collections
from collections import defaultdict
from dataclasses import dataclass
import typing
import math
import resource
import unicodedata

import shared
from shared import spec, stderr, print_tree
from HTML import HNode
from Pseudocode_Parser import ANode
from es_parser import ParseNode, ParseError, T_lit, parse
from DecoratedFuncDict import DecoratedFuncDict
import unicode_contributory_properties as ucp

# -------------------------------
# This code gets very recursive.

# In test262-parser-tests, I think the worst (deepest) case is pass/dd3c63403db5c06e.js:
# ((((((((((((((((((((((((((((((((((((((((((((((((((1))))))))))))))))))))))))))))))))))))))))))))))))))
#
# That's 50 pairs of parens, each of which produces a chain of 22 Parse Nodes,
# so that's 1100 levels of Parse Nodes, plus another 26 for a total of 1126 levels.
#
# When executing the 'AllPrivateIdentifiersValid' SDO,
# each Parse Node level generates about 39 Python stack frames.
# (For 'Contains', it's only about 35.)
#
# 1126 * 39 = 43914

sys.setrecursionlimit(44_000)

# and maybe 455 bytes per Python stack frame
resource.setrlimit(resource.RLIMIT_STACK, (44_000 * 455, resource.RLIM_INFINITY))

# ----

NYI = 0 # Not Yet Implemented

# If an exception is raised (typically via `assert NYI`),
# only the latest few frame are helpful.
sys.tracebacklimit = 3

# -------------------------------

verbosity = 0

# -------------------------------

def detect_early_errors(pnode):
    assert pnode.symbol in ['Script', 'Module']

    # print(get_parse_tree_depth(pnode)); assert 0

    de = DynamicEnvironment()

    # stderr("de.max_frame_stack_len:", de.max_frame_stack_len)

    early_errors = de.get_early_errors_in(pnode)
    return early_errors

def get_parse_tree_depth(pnode):
    if len(pnode.children) == 0:
        return 1
    max_child_depth = max(
        get_parse_tree_depth(child)
        for child in pnode.children
    )
    return 1 + max_child_depth

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

class DynamicEnvironment:
    def __init__(de):
        de.frame_stack = []
        de.max_frame_stack_len = 0

    def curr_frame(de):
        return de.frame_stack[-1]

    # --------------------------------------------------------------------------

    def each(de, each_thing):
        assert not de.curr_frame().is_returning()

        assert isinstance(each_thing, ANode)
        p = str(each_thing.prod)

        if p not in eachd:
            stderr()
            stderr('NEED:')
            stderr(f"@eachd.put({p!r})")
            stderr('for:')
            stderr(each_thing.source_text())
            sys.exit(1)

        func = eachd[p]
        (var, iterable) = func(de, *each_thing.children)

        assert isinstance(var, ANode)
        assert var.prod.lhs_s == '{var}'
        assert isinstance(iterable, collections.abc.Iterable)

        return (var, iterable)

    def get_early_errors_in(de, pnode):
        if hasattr(de, 'early_errors'):
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
            assert not hasattr(de, 'saved_early_errors')
            de.saved_early_errors = de.early_errors

        de.early_errors = []
        de.traverse_for_early_errors(pnode)
        resulting_early_errors = de.early_errors
        del de.early_errors

        if hasattr(de, 'saved_early_errors'):
            de.early_errors = de.saved_early_errors
            del de.saved_early_errors

        return resulting_early_errors

    def traverse_for_early_errors(de, pnode):
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
            if verbosity >= 1:
                stderr(f"\nThere are {len(ee_rules)} Early Error rules for {pnode.puk}:")
            for ee_rule in ee_rules:
                de.execute_alg_defn(ee_rule, focus_node=pnode)

        # check pnode's descendants
        for child in pnode.children:
            de.traverse_for_early_errors(child)

    def exec(de, anode, expected_return):
        frame = de.curr_frame()
        assert not frame.is_returning()

        assert isinstance(anode, ANode)
        p = str(anode.prod)

        if p not in efd:
            stderr()
            stderr('NEED:')
            stderr(f"@efd.put({p!r})")
            stderr('for:')
            stderr(anode.source_text())
            sys.exit(1)

        if frame._is_tracing: stderr(frame._tracing_indentation, f"before {p}")
        func = efd[p]
        result = func(de, *anode.children)
        if frame._is_tracing: stderr(frame._tracing_indentation, f"after {p}, returned {result}")

        if expected_return is None:
            expectation_met = (result is None)
        elif expected_return == 'ParseNodeOrAbsent':
            expectation_met = isinstance(result, (ParseNode, AbsentParseNode))
        elif expected_return in [E_Value, ES_Value]:
            expectation_met = isinstance(result, expected_return) or isinstance(result, ParseNode)
            # ParseNode should be derived from ES_Value, but that's not convenient.
        else:
            expectation_met = isinstance(result, expected_return)

        if not expectation_met:
            # Maybe we can do an implicit conversion
            if expected_return in [ES_Mathnum, (ES_Mathnum,EL_Number)] and isinstance(result, ES_UnicodeCodePoint):
                if verbosity >= 1: stderr("Implicitly converting ES_UnicodeCodePoint to ES_Mathnum")
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

    def execute_alg_defn(de, alg_defn, **kwargs):
        frame = Frame(alg_defn, **kwargs)

        L = len(de.frame_stack)
        indentation = ' ' * (2 + L)
        if verbosity >= 2: stderr(indentation + 'v', frame._slug)

        frame._tracing_indentation = indentation
        frame._is_tracing = True and (
            frame._slug == 'Early Errors on <ParseNode symbol=UnaryExpression, 2 children>'
        )

        if 0:
            print('len(de.frame_stack):', L)
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

        de.frame_stack.append(frame)
        if len(de.frame_stack) > de.max_frame_stack_len:
            de.max_frame_stack_len = len(de.frame_stack)
        result = frame.run(de)
        rframe = de.frame_stack.pop()
        assert rframe is frame

        if verbosity >= 2: stderr(indentation + '^', frame._slug, 'returns', result)
        return result

    def it_is_a_syntax_error(de, rule):
        if isinstance(rule, ANode): rule = rule.source_text()
        error = EarlyError('Syntax Error', de.curr_frame()._focus_node, rule)
        de.early_errors.append(error)
        if verbosity >= 1: stderr(f"Found early error: {error}")

class Frame:
    def __init__(frame, alg_defn, *, focus_node=None, arg_vals=[]):
        # -----
        # alg_defn:

        frame._alg_defn = alg_defn
        frame._header = alg_defn.header
        frame._alg = alg_defn.header.parent_alg

        # -----------
        # focus_node:

        frame._focus_node = focus_node
        if frame._alg.species.startswith('op: discriminated by syntax'):
            assert frame._focus_node is not None
            assert isinstance(frame._focus_node, ParseNode)
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
            assert len(arg_vals) == len(frame._header.param_names)
            # XXX Doesn't handle optionals yet.
            for (param_name, arg_val) in zip(frame._header.param_names, arg_vals):
                frame.let_var_be_value(param_name, arg_val)
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
                    ref_node = AbsentParseNode() # ParseNode(T_named('*OMITTED_OPTIONAL*'), (0,0), tip)
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

    def run(frame, de):
        anode = frame._alg_defn.anode
        # stderr('   ', anode.source_text())

        s = anode.prod.lhs_s
        if s == '{EE_RULE}':
            try:
                de.exec(anode, None)
            except ReferenceToNonexistentThing:
                # The rule just fails to find an early error.
                pass
            assert not frame.is_returning()
            result = None

        elif s == '{EMU_ALG_BODY}':
            try:
                de.exec(anode, None)
                assert frame.is_returning()
                result = frame.return_value
            except ReferenceToNonexistentThing:
                result = {
                    'Contains'  : EL_Boolean(False),
                    'BoundNames': ES_List([]),
                }[frame._alg.name]

        elif s == '{EXPR}':
            result = de.exec(anode, E_Value)

        elif s == '{ONE_LINE_ALG}':
            de.exec(anode, None)
            assert frame.is_returning()
            result = frame.return_value

        else:
            assert 0, s

        return result

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

    def let_var_be_value(frame, var, value):
        if isinstance(var, str):
            varname = var
        elif isinstance(var, ANode):
            [varname] = var.children
        else:
            assert 0, var
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
            return AbsentParseNode()

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

        if isinstance(referent, ParseNode):
            assert referent.symbol == nt_name
        elif isinstance(referent, AbsentParseNode):
            pass
        else:
            assert 0
        return referent

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

efd = DecoratedFuncDict()
# execution function dictionary

eachd = DecoratedFuncDict()

predefined_operations = DecoratedFuncDict()

def report_unused_things():
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

    dfd_report_unused_entries('efd', efd)
    dfd_report_unused_entries('eachd', eachd)
    dfd_report_unused_entries('predefined_operations', predefined_operations)

# Have to declare these up here, otherwise there would be forward references.
class E_Value: pass # ECMAScript value
class EL_Value(E_Value): pass # ECMAScript language value
class ES_Value(E_Value): pass # ECMAScript specification value

# ==============================================================================

@efd.put('{EMU_ALG_BODY} : {IND_COMMANDS}{nlai}')
@efd.put('{IND_COMMANDS} : {_indent_}{COMMANDS}{_outdent_}')
@efd.put('{COMMANDS} : {_NL_N} {COMMAND}')
@efd.put('{COMMAND} : {IF_OTHER}')
@efd.put('{COMMAND} : {IF_CLOSED}')
@efd.put('{ONE_LINE_ALG} : {nlai}{COMMAND}{nlai}')
def _(de, comm):
    de.exec(comm, None)

@efd.put('{COMMANDS} : {COMMANDS}{_NL_N} {COMMAND}')
def _(de, commands, command):
    de.exec(commands, None)
    if de.curr_frame().is_returning(): return
    de.exec(command, None)

@efd.put('{COMMAND} : Return {EXPR}.')
@efd.put('{SMALL_COMMAND} : return {EXPR}')
def _(de, expr):
    de.curr_frame().start_returning(de.exec(expr, E_Value))

# ==============================================================================

@efd.put('{CONDITION} : {CONDITION_1}')
@efd.put('{CONDITION_1} : {NUM_COMPARISON}')
def _(de, subcond):
    return de.exec(subcond, bool)

@efd.put('{CONDITION} : {CONDITION_1} unless {CONDITION_1}')
@efd.put('{CONDITION} : {CONDITION_1}, unless {CONDITION_1}')
def _(de, conda, condb):
    return de.exec(conda, bool) and not de.exec(condb, bool)

@efd.put('{CONDITION} : {CONDITION_1} and {CONDITION_1}')
def _(de, conda, condb):
    return de.exec(conda, bool) and de.exec(condb, bool)

@efd.put('{CONDITION} : {CONDITION_1} or if {CONDITION_1}')
@efd.put('{CONDITION} : either {CONDITION_1} or {CONDITION_1}')
def _(de, conda, condb):
    return de.exec(conda, bool) or de.exec(condb, bool)

# ==============================================================================

@efd.put('{EXPR} : {EX}')
@efd.put('{EXPR} : {PP_NAMED_OPERATION_INVOCATION}')
@efd.put('{EX} : ({EX})')
@efd.put('{EX} : {LITERAL}')
@efd.put('{EX} : {LOCAL_REF}')
@efd.put('{LITERAL} : {BOOL_LITERAL}')
@efd.put('{LITERAL} : {starred_str}')
@efd.put('{LITERAL} : {tilded_word}')
@efd.put('{LOCAL_REF} : {PROD_REF}')
@efd.put('{LOCAL_REF} : {SETTABLE}')
@efd.put('{NUM_COMPARAND} : {FACTOR}')
@efd.put('{SETTABLE} : {var}')
def _(de, child):
    return de.exec(child, E_Value)

# ==============================================================================

# Functions for dealing with spec markup?

def dereference_emu_xref(emu_xref):
    assert isinstance(emu_xref, ANode)
    assert emu_xref.prod.lhs_s == '{h_emu_xref}'
    st = emu_xref.source_text()
    mo = re.fullmatch('<emu-xref href="#([^"]+)"></emu-xref>', st)
    assert mo
    id = mo.group(1)
    return spec.node_with_id_[id]

def emu_table_get_unique_row_satisfying(emu_table, predicate):
    assert isinstance(emu_table, HNode)
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

# 5.1 Syntactic and Lexical Grammars

# ------------------------------------------------------------------------------
# 5.1.1 Context-Free Grammars

#> A <em>context-free grammar</em> consists of a number of <em>productions</em>.
#> Each production has an abstract symbol called a <em>nonterminal</em>
#> as its <em>left-hand side</em>,
#> and a sequence of zero or more nonterminal and <em>terminal</em> symbols
#> as its <em>right-hand side</em>.
#> For each grammar, the terminal symbols are drawn from a specified alphabet.</p>

class ES_GrammarSymbol(ES_Value): pass

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

@dataclass(frozen=True)
class ES_NonterminalSymbol(ES_GrammarSymbol):
    name: str

@efd.put('{G_SYM} : {TERMINAL}')
def _(de, terminal):
    return ES_TerminalSymbol.from_TERMINAL_anode(terminal)

@efd.put('{G_SYM} : {nonterminal}')
def _(de, nonterminal):
    [nont_str] = nonterminal.children
    assert nont_str.startswith('|')
    assert nont_str.endswith('|')
    return ES_NonterminalSymbol(nont_str[1:-1])

@efd.put('{nonterminal} : \\| [A-Za-z][A-Za-z0-9]* (_opt|\\?)? (\\[ .+? \\])? \\|')
def _(de, chars):
    return ES_NonterminalSymbol(chars[1:-1])

@efd.put('{CONDITION_1} : {var} is not one of {nonterminal}, {nonterminal}, {nonterminal}, `super` or `this`')
def _(de, var, nonta, nontb, nontc):
    gsym = de.exec(var, ES_GrammarSymbol)
    return gsym not in [
        ES_NonterminalSymbol(nt_name_from_nonterminal_node(nonta)),
        ES_NonterminalSymbol(nt_name_from_nonterminal_node(nontb)),
        ES_NonterminalSymbol(nt_name_from_nonterminal_node(nontc)),
        ES_TerminalSymbol('super'),
        ES_TerminalSymbol('this'),
    ]

@efd.put('{CONDITION_1} : {var} is {nonterminal}')
def _(de, var, nont):
    var_sym = de.exec(var, ES_GrammarSymbol)
    nont_sym = ES_NonterminalSymbol(nt_name_from_nonterminal_node(nont))
    return var_sym == nont_sym

def nt_name_from_nonterminal_node(nonterminal_node):
    assert isinstance(nonterminal_node, ANode)
    nonterminal_node.prod.lhs_s == 'nonterminal'
    [nonterminal_str] = nonterminal_node.children
    assert nonterminal_str.startswith('|')
    assert nonterminal_str.endswith('|')
    return nonterminal_str[1:-1]

# ------------------------------------------------------------------------------
# 5.1.4 The Syntactic Grammar

#> When a stream of code points is to be parsed as an ECMAScript |Script| or |Module|, ...

#> When a parse is successful, it constructs a parse tree,
#> a rooted tree structure in which each node is a <dfn>Parse Node</dfn>.
#> Each Parse Node is an <em>instance</em> of a symbol in the grammar;
#> it represents a span of the source text that can be derived from that symbol.

class AbsentParseNode(ES_Value): pass

@efd.put('{CONDITION_1} : {var} is a Parse Node')
def _(de, var):
    x = de.exec(var, E_Value)
    return isinstance(x, ParseNode)

# -----
# explicitly use "an instance of":

@efd.put('{CONDITION_1} : {var} is an instance of {var}')
def _(de, vara, varb):
    node = de.exec(vara, ParseNode)
    gsym = de.exec(varb, ES_GrammarSymbol)
    if isinstance(gsym, ES_TerminalSymbol):
        node_symbol = T_lit(gsym.chars)
        # Theoretically, it could be a different kind of T_foo,
        # but so far, the only case of this is `super`.
    elif isinstance(gsym, ES_NonterminalSymbol):
        node_symbol = gsym.name
    else:
        assert 0
    return node.symbol == node_symbol

@efd.put('{CONDITION_1} : {var} is an instance of a nonterminal')
def _(de, var):
    node = de.exec(var, ParseNode)
    return not node.is_terminal

# -----
# implicitly use "an instance of": (should the spec make it explicit?)

@efd.put('{CONDITION_1} : {LOCAL_REF} is {h_emu_grammar}')  # early_error
@efd.put('{CONDITION_1} : {LOCAL_REF} is {h_emu_grammar} ') # emu_alg
def _(de, local_ref, h_emu_grammar):
    pnode = de.exec(local_ref, ParseNode)
    result = (pnode.puk in h_emu_grammar._hnode.puk_set)

    # But this can also augment the current focus_map.
    # E.g., in TopLevelVarDeclaredNames,
    #> StatementListItem : Declaration
    #>    1. If |Declaration| is |Declaration : HoistableDeclaration|, then
    #>       a. Return the BoundNames of |HoistableDeclaration|.
    de.curr_frame().augment_focus_map(pnode)

    return result

@efd.put('{CONDITION_1} : {LOCAL_REF} is {h_emu_grammar}, {h_emu_grammar}, {h_emu_grammar}, {h_emu_grammar}, or {h_emu_grammar}')
def _(de, local_ref, *h_emu_grammar_):
    pnode = de.exec(local_ref, ParseNode)
    result = any(
        pnode_unit_derives_a_node_with_puk(pnode, h_emu_grammar._hnode.puk_set)
        for h_emu_grammar in h_emu_grammar_
    )
    return result

@efd.put('{CONDITION_1} : {var} is an? {nonterminal}')
def _(de, var, nont):
    node = de.exec(var, ParseNode)
    nt_name = nt_name_from_nonterminal_node(nont)
    return (node.symbol == nt_name)

@efd.put('{CONDITION_1} : {var} is not a {nonterminal}')
def _(de, var, nont):
    pnode = de.exec(var, ParseNode)
    nont_sym = ES_NonterminalSymbol(nt_name_from_nonterminal_node(nont))
    return pnode.symbol != nont_sym

@efd.put('{CONDITION_1} : {PROD_REF} is `export` {nonterminal}')
def _(de, prod_ref, nont):
    nt_name = nt_name_from_nonterminal_node(nont)
    pnode = de.exec(prod_ref, ParseNode)
    return (
        len(pnode.children) == 2
        and
        pnode.children[0].symbol == T_lit('export')
        and
        pnode.children[1].symbol == nt_name
    )

@efd.put('{CONDITION_1} : {var} is the {nonterminal} {TERMINAL}')
def _(de, var, nont, terminal):
    assert nont.source_text() == '|ReservedWord|'
    terminal_gsym = ES_TerminalSymbol.from_TERMINAL_anode(terminal)
    var_gsym = de.exec(var, ES_GrammarSymbol)
    return var_gsym == terminal_gsym

@efd.put('{CONDITION_1} : {var} contains a {nonterminal}')
def _(de, var, nont):
    pnode = de.exec(var, ParseNode)
    nt_name = nt_name_from_nonterminal_node(nont)
    return pnode.contains_a(nt_name)

# -----
#> it represents a span of the source text that can be derived from that symbol.

@efd.put('{EXPR} : the source text that was recognized as {PROD_REF}')
def _(de, prod_ref):
    node = de.exec(prod_ref, ParseNode)
    return ES_UnicodeCodePoints(node.text())

@efd.put('{CONDITION_1} : {NAMED_OPERATION_INVOCATION} is a {nonterminal}')
def _(de, noi, nont):
    nt_name = nt_name_from_nonterminal_node(nont)
    assert nt_name == 'ReservedWord'
    # The wording suggests that it's asking whether
    # a Parse Node is an instance of some nonterminal,
    # but it's actually asking
    # whether a String value conforms to the syntax of |ReservedWord|.
    # This question is a bit odd,
    # because |ReservedWord| (like all grammar symbols)
    # defines a syntax for Unicode text, not strings.
    # However, |ReservedWord| only involves Latin letters,
    # so ...
    string_value = de.exec(noi, EL_String)

    # kludge

    if string_value in [
        EL_String.from_Python_string('a'),
        EL_String.from_Python_string('b'),
    ]:
        return False

    assert NYI

# -----

#> Moreover, it has zero or more <em>children</em>,
#> one for each symbol on the production's right-hand side:
#> each child is a Parse Node that is an instance of the corresponding symbol.

@eachd.put('{EACH_THING} : child node {var} of this Parse Node')
def _(de, var):
    pnode = de.curr_frame()._focus_node
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
    return (var, same_tip_children)

# -----

# (It is the `parent` of its children.)
# (By examining the parent of a Parse Node (if any), and that parent's parent, etc,
# we can ...

@efd.put('{CONDITION_1} : {LOCAL_REF} is not nested, directly or indirectly (but not crossing function or `static` initialization block boundaries), within an {nonterminal}')
def _(de, local_ref, nont):
    nt_name = nt_name_from_nonterminal_node(nont)
    pnode = de.exec(local_ref, ParseNode)
    return not node_is_nested_but_not_crossing_function_boundaries_within_a(pnode, [nt_name])

@efd.put('{CONDITION_1} : {LOCAL_REF} is not nested, directly or indirectly (but not crossing function or `static` initialization block boundaries), within an {nonterminal} or a {nonterminal}')
def _(de, local_ref, nonta, nontb):
    nt_name_a = nt_name_from_nonterminal_node(nonta)
    nt_name_b = nt_name_from_nonterminal_node(nontb)
    pnode = de.exec(local_ref, ParseNode)
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

# -----

#> ... In such cases a more restrictive supplemental grammar is provided
#> that further restricts the acceptable token sequences.
#> Typically, an early error rule will then define an error condition
#> if "P is not covering an N",
#> where P is a Parse Node (an instance of the generalized production)
#> and N is a nonterminal from the supplemental grammar.
#> Here, the sequence of tokens originally matched by P
#> is parsed again using N as the goal symbol.
#> (If N takes grammatical parameters, then they are set to
#> the same values used when P was originally parsed.)

@efd.put('{CONDITION_1} : {LOCAL_REF} is not covering an? {nonterminal}')
def _(de, local_ref, nont):
    pnode = de.exec(local_ref, ParseNode)
    covered_thing = the_nonterminal_that_is_covered_by_pnode(nont, pnode)
    return (covered_thing is None)

@efd.put('{EX} : the {nonterminal} that is covered by {LOCAL_REF}')
@efd.put('{EXPR} : the {nonterminal} that is covered by {LOCAL_REF}')
def _(de, nont, local_ref):
    pnode = de.exec(local_ref, ParseNode)
    covered_thing = the_nonterminal_that_is_covered_by_pnode(nont, pnode)
    if covered_thing is None:
        raise ReferenceToNonexistentThing(nont.parent.source_text())
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

class ReferenceToNonexistentThing(BaseException):
    def __init__(self, descr):
        self.descr = descr

# Problem: 
# For example, consider fail/0bee7999482c66a0.js, whose text is `(10) => 0`
#
# This has a early error due to:
#>   ArrowParameters : CoverParenthesizedExpressionAndArrowParameterList
#>     It is a Syntax Error if |CoverParenthesizedExpressionAndArrowParameterList|
#>     is not covering an |ArrowFormalParameters|.
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

# ------------------------------------------------------------------------------
# 5.1.5 Grammar Notation

# grammatical parameters
# (see 5.2.2)

# ------------------------------------------------------------------------------
# 5.2 Algorithm Conventions

#> A step that begins with "Assert:" asserts an invariant condition of its algorithm.
@efd.put('{COMMAND} : Assert: {CONDITION}.')
def _(de, condition):
    cond_value = de.exec(condition, bool)
    assert cond_value is True

#> Algorithm steps may declare named aliases for any value ...
@efd.put('{var} : \\b _ [A-Za-z][A-Za-z0-9]* _ \\b')
def _(de, varname):
    return de.curr_frame().get_value_referenced_by_var(varname)

#> ... using the form "Let x be someValue".
@efd.put('{COMMAND} : Let {var} be {EXPR}.')
@efd.put('{SMALL_COMMAND} : let {var} be {EXPR}')
def _(de, var, expr):
    value = de.exec(expr, E_Value)
    de.curr_frame().let_var_be_value(var, value)

@efd.put('{EXPR} : {EX}, where {var} is {EX}')
def _(de, exa, var, exb):
    value = de.exec(exb, E_Value)
    de.curr_frame().start_contour()
    de.curr_frame().let_var_be_value(var, value)
    result = de.exec(exa, E_Value)
    de.curr_frame().end_contour()
    return result

@efd.put('{LOCAL_REF} : {var}')
def _(de, var):
    return de.exec(var, E_Value)

#> Aliases may be modified using the form "Set x to someOtherValue".
@efd.put('{COMMAND} : Set {SETTABLE} to {EXPR}.')
def _(de, settable, expr):
    value = de.exec(expr, E_Value)
    de.curr_frame().set_settable_to_value(settable, value)

# If-steps aren't defined, but this is presumably where they would be.

@efd.put('{IF_CLOSED} : If {CONDITION}, {SMALL_COMMAND}; otherwise, {SMALL_COMMAND}.')
@efd.put('{IF_CLOSED} : If {CONDITION}, {SMALL_COMMAND}; else {SMALL_COMMAND}.')
def _(de, cond, cmdt, cmdf):
    if de.exec(cond, bool):
        de.exec(cmdt, None)
    else:
        de.exec(cmdf, None)

@efd.put('{IF_OTHER} : {IF_OPEN}{IF_TAIL}')
def _(de, if_open, if_tail):
    [condition, then_commands] = if_open.children
    cond_value = de.exec(condition, bool)
    if cond_value:
        de.exec(then_commands, None)
    else:
        de.exec(if_tail, None)

@efd.put('{IF_TAIL} : {EPSILON}')
def _(de):
    pass

@efd.put('{IF_TAIL} : {_NL_N} {ELSE_PART}')
@efd.put('{ELSE_PART} : Otherwise, {SMALL_COMMAND}.')
@efd.put('{ELSE_PART} : Else, {SMALL_COMMAND}.')
@efd.put('{ELSE_PART} : Else,{IND_COMMANDS}')
def _(de, child):
    de.exec(child, None)

@efd.put('{EXPR} : {EX} if {CONDITION}. Otherwise, it is {EXPR}')
def _(de, exa, cond, exb):
    ex = exa if de.exec(cond, bool) else exb
    return de.exec(ex, E_Value)

# Loops aren't defined, but this is presumably where they would be.

@efd.put('{COMMAND} : For each {EACH_THING}, do{IND_COMMANDS}')
def _(de, each_thing, commands):
    (loop_var, iterable) = de.each(each_thing)
    for value in iterable:
        de.curr_frame().start_contour()
        de.curr_frame().let_var_be_value(loop_var, value)
        de.exec(commands, None)
        de.curr_frame().end_contour()
        if de.curr_frame().is_returning(): return

@eachd.put('{EACH_THING} : {ITEM_NATURE} {var} of {EX}')
def _(de, item_nature, var, ex):
    item_nature_s = item_nature.source_text()
    collection = de.exec(ex, E_Value)
    return (var, collection.each(item_nature_s))

# ------------------------------------------------------------------------------
# 5.2.1 Abstract Operations

@efd.put('{EXPR} : the result of {PP_NAMED_OPERATION_INVOCATION}')
@efd.put('{EX} : {PP_NAMED_OPERATION_INVOCATION}')
@efd.put('{PP_NAMED_OPERATION_INVOCATION} : {NAMED_OPERATION_INVOCATION}')
@efd.put('{EX} : {NAMED_OPERATION_INVOCATION}')
@efd.put('{NAMED_OPERATION_INVOCATION} : {PREFIX_PAREN}')
def _(de, child):
    return de.exec(child, E_Value)

@efd.put('{PREFIX_PAREN} : {OPN_BEFORE_PAREN}({EXLIST_OPT})')
def _(de, opn_before_paren, exlist_opt):
    opr = opn_before_paren.prod.rhs_s
    if opr == '{SIMPLE_OPERATION_NAME}':
        op_name = opn_before_paren.source_text()
    elif opr == '{NUMERIC_TYPE_INDICATOR}::{low_word}':
        [numeric_type_indicator, low_word] = opn_before_paren.children
        [low_word_str] = low_word.children
        if numeric_type_indicator.prod.rhs_s == 'Number':
            op_name = ('Number', low_word_str)
        else:
            assert NYI, numeric_type_indicator
        
    else:
        assert NYI
    #
    arg_values = de.exec(exlist_opt, list)
    return apply_op_to_arg_values(de, op_name, arg_values)

@efd.put('{NAMED_OPERATION_INVOCATION} : {cap_word}({PROD_REF})')
@efd.put('{NAMED_OPERATION_INVOCATION} : the result of performing {cap_word} on {EX}') # looks like an SDO invocation, but it isn't
def _(de, cap_word, arg):
    [op_name] = cap_word.children
    arg_value = de.exec(arg, E_Value)
    return apply_op_to_arg_values(de, op_name, [arg_value])

@efd.put('{EXLIST_OPT} : {EXLIST}')
def _(de, exlist):
    return de.exec(exlist, list)

@efd.put('{EXLIST} : {EX}')
@efd.put('{EXLIST_OPT} : {var}')
def _(de, ex):
    return [ de.exec(ex, E_Value) ]

@efd.put('{EXLIST} : {EXLIST}, {EX}')
def _(de, exlist, ex):
    return de.exec(exlist, list) + [de.exec(ex, E_Value)]

# ----------

def apply_op_to_arg_values(de, op_name, arg_values):
    if isinstance(op_name, str):

        alg_info = spec.alg_info_['op'][op_name]
        assert alg_info.species == 'op: singular'

        alg_defns = alg_info.all_definitions()
        if len(alg_defns) == 0:
            # Pseudocode.py has calls like:
            # ensure_alg('op: singular', 'floor')
            # but no definition(s), so we arrive here.
            func = predefined_operations[op_name]
            return func(de, *arg_values)

        elif len(alg_defns) == 1:
            [alg_defn] = alg_defns
            return de.execute_alg_defn(alg_defn, arg_vals=arg_values)

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

            return de.execute_alg_defn(relevant_alg_defn, arg_vals=arg_values)

    elif isinstance(op_name, tuple):
        assert len(op_name) == 2
        (type_name, method_name) = op_name
        alg_info = spec.alg_info_['op']['::' + method_name]
        assert alg_info.species == 'op: discriminated by type: numeric'
        matching_defns = [
            alg_defn
            for alg_defn in alg_info.all_definitions()
            if alg_defn.discriminator == type_name
        ]
        assert len(matching_defns) == 1
        [relevant_alg_defn] = matching_defns
        return de.execute_alg_defn(relevant_alg_defn, arg_vals=arg_values)

    else:
        assert NYI, op_name

def value_matches_discriminator(value, discriminator):
    assert isinstance(value, E_Value)
    assert isinstance(discriminator, str)
    value_type_name = type(value).__name__
    assert value_type_name.startswith('EL_')
    return (value_type_name == 'EL_' + discriminator)

# ------------------------------------------------------------------------------
# 5.2.2 Syntax-Directed Operations

@efd.put('{NAMED_OPERATION_INVOCATION} : the {cap_word} of {LOCAL_REF}')
@efd.put('{NAMED_OPERATION_INVOCATION} : {cap_word} of {LOCAL_REF}')
@efd.put('{NAMED_OPERATION_INVOCATION} : the {ISDO_NAME} of {PROD_REF}')
def _(de, cap_word, local_ref):
    return execute_sdo_invocation(de, cap_word, local_ref, [])

@efd.put('{NAMED_OPERATION_INVOCATION} : {cap_word} of {LOCAL_REF} {WITH_ARGS}')
@efd.put('{NAMED_OPERATION_INVOCATION} : {cap_word} for {LOCAL_REF} {WITH_ARGS}')
def _(de, cap_word, local_ref, with_args):
    return execute_sdo_invocation(de, cap_word, local_ref, flatten_with_args(with_args))

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

def execute_sdo_invocation(de, sdo_name_arg, focus_expr, arg_exprs):
    focus_node = de.exec(focus_expr, ParseNode)

    arg_vals = [
        de.exec(arg_expr, E_Value)
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

    return de.execute_alg_defn(sdo_defn, focus_node=focus_node, arg_vals=arg_vals)

# -----------------

#> When an algorithm is associated with a grammar production,
#> it may reference the terminal and nonterminal symbols
#> of the production alternative
#> as if they were parameters of the algorithm.

@efd.put('{PROD_REF} : this production')
@efd.put('{PROD_REF} : this phrase')
def _(de):
    return de.curr_frame()._focus_node

@efd.put('{PROD_REF} : this {nonterminal}')
def _(de, nont):
    fn = de.curr_frame()._focus_node
    assert fn.symbol == nt_name_from_nonterminal_node(nont)
    return fn

@efd.put('{PROD_REF} : the {nonterminal} containing this {nonterminal}')
def _(de, container_nont, this_nont):
    fn = de.curr_frame()._focus_node
    assert fn.symbol == nt_name_from_nonterminal_node(this_nont)
    container_nt = nt_name_from_nonterminal_node(container_nont)
    containers = [
        anc
        for anc in fn.each_ancestor()
        if anc.symbol == container_nt
    ]
    assert len(containers) == 1
    return containers[0]

@efd.put('{PROD_REF} : {nonterminal}')
def _(de, nont):
    if de.curr_frame().has_a_focus_node():
        nt_name = nt_name_from_nonterminal_node(nont)
        node = de.curr_frame().resolve_focus_reference(None, nt_name)
        return node
    else:
        # This isn't really a {PROD_REF}, it's a {G_SYM},
        # but we can't make the metagrammar ambiguous.
        return de.exec(nont, ES_NonterminalSymbol)

@efd.put('{PROD_REF} : the {nonterminal}')
def _(de, nont):
    nt_name = nt_name_from_nonterminal_node(nont)
    return de.curr_frame().resolve_focus_reference(None, nt_name)

@efd.put('{PROD_REF} : the {ORDINAL} {nonterminal}')
def _(de, ordinal, nont):
    ordinal_str = ordinal.source_text()
    ordinal_num = {
        'first' : 1,
        'second': 2,
        'third' : 3,
        'fourth': 4,
    }[ordinal_str]
    nt_name = nt_name_from_nonterminal_node(nont)
    return de.curr_frame().resolve_focus_reference(ordinal_num, nt_name)

@efd.put('{PROD_REF} : the derived {nonterminal}')
def _(de, nont):
    nt_name = nt_name_from_nonterminal_node(nont)
    return de.curr_frame().resolve_focus_reference('derived', nt_name)

@efd.put('{CONDITION_1} : {PROD_REF} is present')
@efd.put('{CONDITION_1} : {EX} is present')
def _(de, prod_ref):
    pnode = de.exec(prod_ref, 'ParseNodeOrAbsent')
    return isinstance(pnode, ParseNode)

@efd.put('{CONDITION_1} : {PROD_REF} is not present')
@efd.put('{CONDITION_1} : {EX} is not present')
def _(de, prod_ref):
    pnode = de.exec(prod_ref, 'ParseNodeOrAbsent')
    return isinstance(pnode, AbsentParseNode)

@efd.put('{CONDITION_1} : {PROD_REF} has an? <sub>[{cap_word}]</sub> parameter')
def _(de, prod_ref, cap_word):
    [cap_word_str] = cap_word.children
    pnode = de.exec(prod_ref, ParseNode)
    return (f"+{cap_word_str}" in pnode.production.og_params_setting)

@efd.put('{CONDITION_1} : the <sub>[Tagged]</sub> parameter was not set')
def _(de):
    cap_word_str = 'Tagged'
    pnode = de.curr_frame()._focus_node
    return (f"~{cap_word_str}" in pnode.production.og_params_setting)

@efd.put('{CONDITION_1} : the goal symbol of the syntactic grammar is {nonterminal}')
def _(de, nont):
    nt_name = nt_name_from_nonterminal_node(nont)
    assert nt_name in ['Script', 'Module']

    pnode = de.curr_frame()._focus_node
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

@efd.put('{CONDITION_1} : any source text matches this rule')
def _(de):
    return True

# ------------------------------------------------------------------------------
# 5.2.4 Static Semantics

@dataclass(frozen=True)
class EarlyError:
    kind: str
    location: ParseNode
    condition: ANode

#> A special kind of static semantic rule is an Early Error Rule.

@efd.put('{EE_RULE} : It is an early Syntax Error if {CONDITION}.')
@efd.put('{EE_RULE} : It is a Syntax Error if {CONDITION}.')
@efd.put('{EE_RULE} : It is a Syntax Error if {CONDITION}. Additional early error rules for {G_SYM} within direct eval are defined in {h_emu_xref}.')
@efd.put('{EE_RULE} : It is a Syntax Error if {CONDITION}. Additional early error rules for {G_SYM} in direct eval are defined in {h_emu_xref}.')
def _(de, cond, *_):
    if de.exec(cond, bool):
        de.it_is_a_syntax_error(cond.parent)

@efd.put('{EE_RULE} : If {CONDITION}, it is a Syntax Error if {CONDITION}.')
def _(de, cond1, cond2):
    if de.exec(cond1, bool) and de.exec(cond2, bool):
        de.it_is_a_syntax_error(cond2.parent)

@efd.put('{EE_RULE} : It is a Syntax Error if {CONDITION}. This rule is not applied if {CONDITION}.')
def _(de, conda, condb):
    if not de.exec(condb, bool) and de.exec(conda, bool):
        de.it_is_a_syntax_error(conda.parent)

@efd.put('{EE_RULE} : Always throw a Syntax Error if code matches this production.')
def _(de):
    de.it_is_a_syntax_error('code matches this production')

@efd.put('{EE_RULE} : <p>It is a Syntax Error if {CONDITION_1} and the following algorithm evaluates to {BOOL_LITERAL}:</p>{nlai}{h_emu_alg}')
def _(de, cond, bool_lit, h_emu_alg):
    if de.exec(cond, bool):
        bool_val = de.exec(bool_lit, EL_Boolean)
        emu_alg_body = h_emu_alg._hnode._syntax_tree

        de.exec(emu_alg_body, None)
        assert de.curr_frame().is_returning()
        alg_result = de.curr_frame().return_value
        de.curr_frame().stop_returning()

        if same_value(alg_result, bool_val):
            de.it_is_a_syntax_error(cond.parent)

@efd.put('{EE_RULE} : If {CONDITION}, the Early Error rules for {h_emu_grammar} are applied.')
def _(de, cond, emu_grammar):
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
    assert cond.source_text() == "the source code matching |FormalParameters| is strict mode code"
    assert emu_grammar.source_text() == "<emu-grammar>UniqueFormalParameters : FormalParameters</emu-grammar>"
    # `UniqueFormalParameters : FormalParameters` only has 1 Early Error rule,
    # and it only refers to |FormalParameters|, which *does* have meaning for the focus node.

    if de.exec(cond, bool):
        ee_map = spec.sdo_coverage_map['Early Errors']
        puk = ('UniqueFormalParameters', 'FormalParameters', '')
        ee_rules = ee_map[puk]
        for ee_rule in ee_rules:
            de.execute_alg_defn(ee_rule, focus_node=de.curr_frame()._focus_node)

@efd.put('{EE_RULE} : All Early Error rules for {nonterminal} and its derived productions also apply to {EX}.')
@efd.put('{EE_RULE} : All early error rules for {nonterminal} and its derived productions also apply to {EX}.')
def _(de, nonta, ex):
    assert ex.source_text().startswith('the ' + nonta.source_text() + ' that is covered by ')
    pnode = de.exec(ex, ParseNode)
    de.traverse_for_early_errors(pnode)

@efd.put('{EE_RULE} : <p>It is a Syntax Error if {LOCAL_REF} is{nlai}<br>{nlai}{h_emu_grammar}{nlai}<br>{nlai}and {LOCAL_REF} ultimately derives a phrase that, if used in place of {LOCAL_REF}, would produce a Syntax Error according to these rules. This rule is recursively applied.</p>')
def _(de, local_ref1, h_emu_grammar, local_ref2, local_ref3):
    assert len(h_emu_grammar._hnode.puk_set) == 1
    [puk] = list(h_emu_grammar._hnode.puk_set)
    pnode = de.exec(local_ref1, ParseNode)
    inner_pnode = pnode_unit_derives_a_node_with_puk(pnode, puk)
    if inner_pnode is None: return # no Syntax Error
    # BUG:
    # phrase = resolve local_ref2 wrt inner_pnode
    # "ultimately" derives? 
    # "these rules"?

@efd.put('{EE_RULE} : For each {nonterminal} {var} in {NAMED_OPERATION_INVOCATION}: It is a Syntax Error if {CONDITION}.')
def _(de, nont, var, noi, cond):
    nt_name = nt_name_from_nonterminal_node(nont)
    L = de.exec(noi, ES_List)
    for pnode in L.elements():
        assert pnode.symbol == nt_name

        de.curr_frame().start_contour()
        de.curr_frame().let_var_be_value(var, pnode)
        if de.exec(cond, bool):
            de.it_is_a_syntax_error(cond)
        de.curr_frame().end_contour()

def pnode_unit_derives_a_node_with_puk(pnode, puk_arg):
    # (Make this a ParseNode method?)
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

# ------------------------------------------------------------------------------
# 5.2.5 Mathematical Operations

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

        if rator_s == '&le;':
            return (a.val <= b.val)
        elif rator_s == '&ge;':
            return (a.val >= b.val)
        elif rator_s == '&gt;':
            return (a.val > b.val)

        assert NYI

    def __add__(self, other): return ES_Mathnum(self.val + other.val)
    def __sub__(self, other): return ES_Mathnum(self.val - other.val)
    def __mul__(self, other): return ES_Mathnum(self.val * other.val)
    def __truediv__(self, other): return ES_Mathnum(self.val / other.val)

    def __mod__(self, other):
        assert isinstance(self.val, int)
        assert isinstance(other.val, int)
        assert other.val != 0
        return ES_Mathnum(self.val % other.val)

@efd.put('{dec_int_lit} : \\b [0-9]+ \\b')
def _(de, chars):
    return ES_Mathnum(int(chars, 10))

@efd.put('{hex_int_lit} : \\b 0x [0-9A-F]{2,6} \\b')
def _(de, chars):
    return ES_Mathnum(int(chars, 16))

@efd.put('{NUM_COMPARISON} : {NUM_COMPARAND} {NUM_COMPARATOR} {NUM_COMPARAND}')
def _(de, randA, ratorAB, randB):
    a = de.exec(randA, ES_Mathnum)
    b = de.exec(randB, ES_Mathnum)
    return ES_Mathnum.compare(a, ratorAB, b)

@efd.put('{CONDITION_1} : {var} &ge; 2<sup>32</sup> - 1')
def _(de, var):
    val = de.exec(var, ES_Mathnum)
    return ES_Mathnum.compare(val, '&ge;', ES_Mathnum(pow(2, 32) - 1))

@efd.put('{CONDITION_1} : {NAMED_OPERATION_INVOCATION} is larger than {var} ({h_emu_xref})')
def _(de, noi, var, _):
    l_val = de.exec(noi, ES_Mathnum)
    r_val = de.exec(var, ES_Mathnum)
    return ES_Mathnum.compare(l_val, '&gt;', r_val)

@efd.put('{NUM_COMPARISON} : {NUM_COMPARAND} {NUM_COMPARATOR} {NUM_COMPARAND} {NUM_COMPARATOR} {NUM_COMPARAND}')
def _(de, randA, ratorAB, randB, ratorBC, randC):
    a = de.exec(randA, ES_Mathnum)
    b = de.exec(randB, ES_Mathnum)
    c = de.exec(randC, ES_Mathnum)
    return ES_Mathnum.compare(a, ratorAB, b) and ES_Mathnum.compare(b, ratorBC, c)

@efd.put('{SUM} : {SUM} {SUM_OPERATOR} {TERM}')
@efd.put('{SUM} : {TERM} {SUM_OPERATOR} {TERM}')
@efd.put('{PRODUCT} : {FACTOR} {PRODUCT_OPERATOR} {FACTOR}')
def _(de, randA, rator, randB):
    op = rator.source_text()
    a = de.exec(randA, ES_Mathnum)
    b = de.exec(randB, ES_Mathnum)
    if op in ['+', 'plus']: return a + b
    elif op in ['&times;', 'times']: return a * b
    elif op == '-': return a - b
    elif op == '/': return a / b
    else:
        assert NYI, op

#> Conversions between mathematical values and Numbers or BigInts
#> are always explicit in this document.
#> A conversion from a mathematical value or extended mathematical value _x_
#> to a Number is denoted as "the Number value for _x_" or {fancy_f}(_x_),
#> and is defined in <emu-xref href="#sec-ecmascript-language-types-number-type"></emu-xref>.

@predefined_operations.put('\U0001d53d')
def _(de, mathnum):
    return the_Number_value_for(mathnum)

#> A conversion from an integer _x_ to a BigInt
#> is denoted as "the BigInt value for _x_" or {fancy_z}(_x_).

#> A conversion from a Number or BigInt _x_ to a mathematical value
#> is denoted as "the mathematical value of _x_", or {fancy_R}(_x_).
#> The mathematical value of *+0*<sub>{fancy_f}</sub> and *-0*<sub>{fancy_f}</sub>
#> is the mathematical value 0.
#> The mathematical value of non-finite values is not defined.
#> The extended mathematical value of _x_
#> is the mathematical value of _x_ for finite values,
#> and is +&infin; and -&infin; for *+&infin;*<sub>{fancy_f}</sub> and *-&infin;*<sub>{fancy_f}</sub> respectively;
#> it is not defined for *NaN*.

#> The mathematical function abs(_x_) ...
#> The mathematical function min(_x1_, _x2_, &hellip; , _xN_) ...
#> The mathematical function max(_x1_, _x2_, ..., _xN_) ...

#> The notation "_x_ modulo _y_" (_y_ must be finite and non-zero)
#> computes a value _k_ of the same sign as _y_ (or zero) such that
#> abs(_k_) < abs(_y_) and _x_ - _k_ = _q_ * _y_ for some integer _q_.
@efd.put('{PRODUCT} : {FACTOR} modulo {FACTOR}')
def _(de, randA, randB):
    a = de.exec(randA, ES_Mathnum)
    b = de.exec(randB, ES_Mathnum)
    return a % b

#> The mathematical function floor(_x_) produces the largest integer
#> (closest to +&infin;) that is not larger than _x_.
@predefined_operations.put('floor')
def _(de, mathnum):
    assert isinstance(mathnum, ES_Mathnum)
    return ES_Mathnum(math.floor(mathnum.val))

#> Mathematical functions min, max, abs, and floor
#> are not defined for Numbers and BigInts,
#> and any usage of those methods that have non-mathematical value arguments
#> would be an editorial error in this specification.

@efd.put('{FACTOR} : {BASE}<sup>{EX}</sup>')
def _(de, base_expr, exponent_expr):
    base_val = de.exec(base_expr, ES_Mathnum)
    exponent_val = de.exec(exponent_expr, ES_Mathnum)
    return ES_Mathnum(base_val.val ** exponent_val.val)

@efd.put('{BASE} : 10')
def _(de):
    return ES_Mathnum(10)

@efd.put('{EX} : {NUM_EXPR}')
@efd.put('{EX} : {NUM_LITERAL}')
@efd.put('{EX} : {PRODUCT}')
@efd.put('{EX} : {SUM}')
@efd.put('{EX} : {var}')
@efd.put('{FACTOR} : ({NUM_EXPR})')
@efd.put('{FACTOR} : {NAMED_OPERATION_INVOCATION}')
@efd.put('{FACTOR} : {NUM_LITERAL}')
@efd.put('{FACTOR} : {PP_NAMED_OPERATION_INVOCATION}')
@efd.put('{FACTOR} : {SETTABLE}')
@efd.put('{LITERAL} : {NUM_LITERAL}')
@efd.put('{NUM_EXPR} : {PRODUCT}')
@efd.put('{NUM_EXPR} : {SUM}')
@efd.put('{TERM} : ({PRODUCT})')
@efd.put('{TERM} : {FACTOR}')
@efd.put('{TERM} : {PRODUCT}')
def _(de, child):
    return de.exec(child, (ES_Mathnum, EL_Number)) # , EL_BigInt))

@efd.put('{NUM_LITERAL} : {dec_int_lit}')
@efd.put('{NUM_LITERAL} : {hex_int_lit}')
def _(de, child):
    return de.exec(child, ES_Mathnum)

# decimal representation

@efd.put('{CONDITION_1} : the decimal representation of {var} has 20 or fewer significant digits')
def _(de, var):
    mathnum = de.exec(var, ES_Mathnum)
    return number_of_significant_digits_in_decimal_representation_of(mathnum) <= 20

def number_of_significant_digits_in_decimal_representation_of(mathnum: ES_Mathnum):
    s = str(mathnum.val).replace('.', '')
    assert s.isdigit()
    return len(s.strip('0'))

# ------------------------------------------------------------------------------
# 5.2.6 Value Notation

#> Values which are internal to the specification
#> and not directly observable from ECMAScript code
#> are indicated with a ~sans-serif~ typeface.

@dataclass(frozen=True)
class ES_Adhoc(ES_Value):
    chars: str

@efd.put('{tilded_word} : ~ [-A-Za-z0-9+]+ ~')
def _(de, chars):
    return ES_Adhoc(chars)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# 6 ECMAScript Data Types and Values

def same_value(a, b):
    assert isinstance(a, (E_Value, ParseNode))
    assert isinstance(b, (E_Value, ParseNode))
    if type(a) == type(b):
        return a == b
    else:
        return False

@efd.put('{CONDITION_1} : {EX} is {LITERAL}')
@efd.put('{CONDITION_1} : {NAMED_OPERATION_INVOCATION} is {LITERAL}')
@efd.put('{CONDITION_1} : {NAMED_OPERATION_INVOCATION} is {U_LITERAL}')
def _(de, ex, literal):
    ex_val = de.exec(ex, E_Value)
    lit_val = de.exec(literal, E_Value)
    return same_value(ex_val, lit_val)

@efd.put('{CONDITION_1} : {EX} is not {LITERAL}')
@efd.put('{CONDITION_1} : {NAMED_OPERATION_INVOCATION} is not {LITERAL}')
def _(de, ex, literal):
    ex_val = de.exec(ex, E_Value)
    lit_val = de.exec(literal, E_Value)
    return not same_value(ex_val, lit_val)

@efd.put('{CONDITION_1} : {NAMED_OPERATION_INVOCATION} is {starred_str} or {starred_str}')
@efd.put('{CONDITION_1} : {EX} is {LITERAL} or {LITERAL}')
def _(de, expr, lita, litb):
    expr_val = de.exec(expr, E_Value)
    lita_val = de.exec(lita, EL_String)
    litb_val = de.exec(litb, EL_String)
    return (
        same_value(expr_val, lita_val)
        or
        same_value(expr_val, litb_val)
    )

@efd.put('{CONDITION_1} : {NAMED_OPERATION_INVOCATION} is: {starred_str}, {starred_str}, {starred_str}, {starred_str}, {starred_str}, {starred_str}, {starred_str}, {starred_str}, or {starred_str}')
def _(de, noi, *starred_strs):
    noi_val = de.exec(noi, E_Value)
    string_values = [
        de.exec(starred_str, EL_String)
        for starred_str in starred_strs
    ]
    return any(
        same_value(noi_val, string_value)
        for string_value in string_values
    )

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# 6.1 ECMAScript Language Types

# ------------------------------------------------------------------------------
# 6.1.1 The Undefined Type

@dataclass(frozen=True)
class EL_Undefined(EL_Value):
    pass

@efd.put('{U_LITERAL} : *undefined*')
def _(de):
    return EL_Undefined()

@efd.put('{EX} : {U_LITERAL}')
def _(de, literal):
    return de.exec(literal, EL_Undefined)

# ------------------------------------------------------------------------------
# 6.1.3 The Boolean Type

@dataclass(frozen=True)
class EL_Boolean(EL_Value):
    b: bool

@efd.put('{LITERAL} : *true*')
@efd.put('{BOOL_LITERAL} : *true*')
def _(de):
    return EL_Boolean(True)

@efd.put('{LITERAL} : *false*')
@efd.put('{BOOL_LITERAL} : *false*')
def _(de):
    return EL_Boolean(False)

# ------------------------------------------------------------------------------
# 6.1.4 The String Type

@dataclass(frozen=True)
class ES_CodeUnit(E_Value):
    numeric_value: int
    def __init__(self, numeric_value):
        assert isinstance(numeric_value, int)
        assert 0 <= numeric_value < 2 ** 16
        object.__setattr__(self, 'numeric_value', numeric_value)

@efd.put('{EX} : {code_unit_lit}')
def _(de, child):
    return de.exec(child, ES_CodeUnit)

@efd.put('{EX} : the code unit whose value is {EX}')
@efd.put('{EXPR} : the code unit whose value is {NAMED_OPERATION_INVOCATION}')
def _(de, ex):
    m = de.exec(ex, ES_Mathnum)
    return ES_CodeUnit(m.val)

@efd.put('{code_unit_lit} : the \\x20 code \\x20 unit \\x20 0x [0-9A-F]{4} \\x20 \\( [A-Z -]+ \\)')
def _(de, chars):
    mo = re.fullmatch(r'the code unit 0x([0-9A-F]{4}) \([A-Z -]+\)', chars)
    assert mo
    cu_hex = mo.group(1)
    cu_int = int(cu_hex, 16)
    return ES_CodeUnit(cu_int)

@efd.put('{EXPR} : the code unit whose value is determined by {PROD_REF} according to {h_emu_xref}')
def _(de, prod_ref, emu_xref):
    pnode = de.exec(prod_ref, ParseNode)
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

# ---------------

@dataclass
class EL_String(EL_Value):
    code_units: typing.List[ES_CodeUnit]

    def __init__(self, code_units):
        assert isinstance(code_units, list)
        for code_unit in code_units:
            assert isinstance(code_unit, ES_CodeUnit)
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

@efd.put('{STR_LITERAL} : the empty String')
def _(de):
    return EL_String([])

@efd.put('{EXPR} : the sequence of code points resulting from interpreting each of the 16-bit elements of {var} as a Unicode BMP code point. UTF-16 decoding is not applied to the elements')
def _(de, var):
    string = de.exec(var, EL_String)
    # This breaks encapsulation on EL_String *and* ES_UnicodeCodePoints:
    text = ''.join(
        chr(code_unit.numeric_value)
        for code_unit in string.code_units
    )
    return ES_UnicodeCodePoints(text)

#> In this specification, the phrase "the string-concatenation of A, B, ..."
#> (where each argument is a String value, a code unit, or a sequence of code units)
#> denotes the String value whose sequence of code units
#> is the concatenation of the code units (in order)
#> of each of the arguments (in order).
@efd.put('{EXPR} : the string-concatenation of {EX} and {EX}')
def _(de, ex1, ex2):
    val1 = de.exec(ex1, (EL_String, ES_CodeUnit))
    val2 = de.exec(ex2, (EL_String, ES_CodeUnit))
    code_units1 = [val1] if isinstance(val1, ES_CodeUnit) else val1.code_units
    code_units2 = [val2] if isinstance(val2, ES_CodeUnit) else val2.code_units
    return EL_String(code_units1 + code_units2)

@efd.put('{EXPR} : the String value consisting of {EX}')
@efd.put('{EXPR} : the String value consisting of {EXPR}')
def _(de, ex):
    val = de.exec(ex, ES_CodeUnit)
    return EL_String([val])

@efd.put('{starred_str} : \\* " ( [^"*] | \\\\ \\* )* " \\*')
def _(de, chars):
    inner_chars = chars[2:-2]
    true_chars = inner_chars.replace('\\*', '*')
    return EL_String.from_Python_string(true_chars)

@efd.put('{CONDITION_1} : {NAMED_OPERATION_INVOCATION} is the same String value as the StringValue of any |ReservedWord| except for `yield` or `await`')
def _(de, noi):
    st = de.exec(noi, EL_String)

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

@efd.put('{CONDITION_1} : {NAMED_OPERATION_INVOCATION} is one of: {starred_str}, {starred_str}, {starred_str}, {starred_str}, {starred_str}, {starred_str}, {starred_str}, or {starred_str}')
def _(de, noi, *starred_strs):
    string_value = de.exec(noi, EL_String)
    for starred_str in starred_strs:
        string_value2 = de.exec(starred_str, EL_String)
        if same_value(string_value, string_value2):
            return True
    return False

@efd.put('{EX} : {STR_LITERAL}')
@efd.put('{LITERAL} : {STR_LITERAL}')
@efd.put('{STR_LITERAL} : {starred_str}')
@efd.put('{STR_LITERAL} : the String {starred_str}')
def _(de, child):
    return de.exec(child, EL_String)

# ------------------------------------------------------------------------------
# 6.1.6.1 The Number Type

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

@efd.put('{starred_nan_lit} : \\* NaN \\*')
def _(de, chars):
    return EL_Number('not a number')

@efd.put('{NUM_LITERAL} : {starred_nan_lit}')
def _(de, child):
    return de.exec(child, EL_Number)

#> In this specification, the phrase "the Number value for _x_"
#> where _x_ represents an exact real mathematical quantity
#> (which might even be an irrational number such as &pi;)
#> means a Number value chosen in the following manner. ...

def the_Number_value_for(mathnum: ES_Mathnum):
    max_safe_integer = 2**53 - 1
    if isinstance(mathnum.val, int):
        if 0 <= mathnum.val < max_safe_integer:
            return EL_Number(('+', mathnum.val))
        
    if mathnum.val >= 2**1024:
        return EL_Number('positive infinity')

    assert NYI, mathnum

# ------------------------------------------------------------------------------
# 6.1.7 The Object Type

@dataclass # not frozen
class Property: # ES_Property(ES_Value) ?
    pass

@dataclass # not frozen
class EL_Object(EL_Value):
    properties: typing.List[Property]

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# 6.2 ECMAScript Specification Types

# ------------------------------------------------------------------------------
# 6.2.1 The List Specification Type

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
            assert isinstance(alist, ES_List)
            all_elements.extend(alist._elements)
        return ES_List(all_elements)

    # modify:

    def append_one(self, element):
        assert isinstance(element, E_Value)
        self._elements.append(element)

    def append_many(self, other):
        assert isinstance(other, ES_List)
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

# make a List:

@efd.put('{EXPR} : a new empty List')
@efd.put('{EX} : &laquo; &raquo;')
def _(de):
    return ES_List([])

@efd.put('{EX} : &laquo; {EXLIST} &raquo;')
def _(de, exlist):
    values = de.exec(exlist, list)
    return ES_List(values)

@efd.put('{EXPR} : a List whose sole element is {EX}')
def _(de, ex):
    value = de.exec(ex, E_Value)
    return ES_List([value])

@efd.put('{EXPR} : a copy of {var}')
def _(de, var):
    # It could, of course, be something other than a List,
    # but in practice, Lists are the only things we copy?
    L = de.exec(var, ES_List)
    return L.copy()

@efd.put('{EXPR} : the list-concatenation of {EX} and {EX}')
def _(de, vara, varb):
    lista = de.exec(vara, ES_List)
    listb = de.exec(varb, ES_List)
    return ES_List.concat(lista, listb)

@efd.put('{EXPR} : the list-concatenation of {var}, {var}, and {var}')
def _(de, vara, varb, varc):
    lista = de.exec(vara, ES_List)
    listb = de.exec(varb, ES_List)
    listc = de.exec(varc, ES_List)
    return ES_List.concat(lista, listb, listc)

# modify a List:

@efd.put('{SMALL_COMMAND} : append {EX} to {var}')
def _(de, item_ex, list_var):
    v = de.exec(item_ex, E_Value)
    L = de.exec(list_var, ES_List)
    L.append_one(v)

# ask questions about a List (or Lists):

@efd.put('{CONDITION_1} : {NAMED_OPERATION_INVOCATION} is not empty')
def _(de, noi):
    L = de.exec(noi, ES_List)
    return not L.is_empty()

@efd.put('{CONDITION_1} : {NAMED_OPERATION_INVOCATION} contains any duplicate entries')
@efd.put('{CONDITION_1} : {NAMED_OPERATION_INVOCATION} contains any duplicate elements')
def _(de, noi):
    L = de.exec(noi, ES_List)
    return L.contains_any_duplicates()

@efd.put('{CONDITION_1} : {NAMED_OPERATION_INVOCATION} contains {starred_str}')
def _(de, noi, starred_str):
    L = de.exec(noi, ES_List)
    s = de.exec(starred_str, EL_String)
    return L.contains(s)

@efd.put('{CONDITION_1} : {var} does not include the element {LITERAL}')
def _(de, var, lit):
    L = de.exec(var, ES_List)
    v = de.exec(lit, E_Value)
    return not L.contains(v)

@efd.put('{CONDITION_1} : {EX} is an element of {var}')
def _(de, ex, var):
    v = de.exec(ex, E_Value)
    L = de.exec(var, ES_List)
    return L.contains(v)

@efd.put('{CONDITION_1} : {EX} is not an element of {var}')
def _(de, ex, var):
    v = de.exec(ex, E_Value)
    L = de.exec(var, ES_List)
    return not L.contains(v)

@efd.put('{CONDITION_1} : {NAMED_OPERATION_INVOCATION} contains more than one occurrence of {starred_str}')
@efd.put('{CONDITION_1} : {NAMED_OPERATION_INVOCATION} contains any duplicate entries for {starred_str}')
def _(de, noi, ss):
    L = de.exec(noi, ES_List)
    v = de.exec(ss, E_Value)
    return L.number_of_occurrences_of(v) > 1

@efd.put('{CONDITION_1} : any element of {NAMED_OPERATION_INVOCATION} also occurs in {NAMED_OPERATION_INVOCATION}')
def _(de, noi1, noi2):
    L1 = de.exec(noi1, ES_List)
    L2 = de.exec(noi2, ES_List)
    return L1.has_any_element_in_common_with(L2)

@efd.put('{CONDITION_1} : any element of {NAMED_OPERATION_INVOCATION} does not also occur in either {NAMED_OPERATION_INVOCATION}, or {NAMED_OPERATION_INVOCATION}')
def _(de, noi1, noi2, noi3):
    L1 = de.exec(noi1, ES_List)
    L2 = de.exec(noi2, ES_List)
    L3 = de.exec(noi3, ES_List)
    return any(
        not (L2.contains(element) or L3.contains(element))
        for element in L1.elements()
    )

@efd.put('{CONDITION_1} : the number of elements in the result of {NAMED_OPERATION_INVOCATION} is greater than 2<sup>32</sup> - 1')
def _(de, noi):
    noi_val = de.exec(noi, ES_List)
    n = noi_val.number_of_elements()
    return ES_Mathnum.compare(n, '&gt;', ES_Mathnum(pow(2, 32) - 1))

# ------------------------------------------------------------------------------
# 6.2.1 The Record Specification Type

class ES_Record(ES_Value):
    pass

# ------------------------------------------------------------------------------
# 6.2.3 The Completion Record Specification Type

class ES_CompletionRecord(ES_Record):
    pass

@efd.put('{PP_NAMED_OPERATION_INVOCATION} : ! {NAMED_OPERATION_INVOCATION}')
def _(de, noi):
    value = de.exec(noi, E_Value)
    if isinstance(value, ES_CompletionRecord):
        assert not value.is_abrupt()
        return value.get_value_of_field_named('[[Value]]')
    else:
        return value

# ------------------------------------------------------------------------------
# ES_UnicodeCodePoint

@dataclass(frozen=True)
class ES_UnicodeCodePoint(ES_Value):
    scalar: int
    def __init__(self, scalar):
        assert 0 <= scalar <= 0x10ffff
        object.__setattr__(self, 'scalar', scalar)

@efd.put('{EX} : the code point value of {PROD_REF}') # the numeric value of the code point ...
def _(de, prod_ref):
    pnode = de.exec(prod_ref, ParseNode)
    assert pnode.symbol == 'SourceCharacter'
    t = pnode.text()
    assert len(t) == 1
    return ES_Mathnum(ord(t))

@efd.put('{EXPR} : the code point matched by {PROD_REF}')
def _(de, prod_ref):
    pnode = de.exec(prod_ref, ParseNode)
    t = pnode.text()
    assert len(t) == 1
    return ES_UnicodeCodePoint(ord(t))

@efd.put('{EXPR} : the code point whose numeric value is {NAMED_OPERATION_INVOCATION}')
def _(de, noi):
    mathnum = de.exec(noi, ES_Mathnum)
    return ES_UnicodeCodePoint(mathnum.val)

@efd.put('{CONDITION_1} : {NAMED_OPERATION_INVOCATION} is not some Unicode code point matched by the {nonterminal} lexical grammar production')
def _(de, noi, nont):
    code_point = de.exec(noi, ES_UnicodeCodePoint)
    nt_name = nt_name_from_nonterminal_node(nont)
    return not pychar_matches_lexical_nonterminal(chr(code_point.scalar), nt_name)

# ----------------------------------------------------------

def pychar_matches_lexical_nonterminal(pychar, nt_name):
    g = spec.grammar_[('lexical', 'A')]
    for rhs in g.prodn_for_lhs_[nt_name]._rhss:
        if pychar_matches_rhs(pychar, rhs):
            return True
    return False

# ----------------------------------------------------------

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
# ES_UnicodeCodePoints

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
        assert isinstance(code_point, ES_UnicodeCodePoint)
        return chr(code_point.scalar) in self.text

    def contains_any_code_points_other_than(self, allowed_code_points):
        return any(
            ES_UnicodeCodePoint(ord(char)) not in allowed_code_points
            for char in self.text
        )

    def contains_the_same_code_point_more_than_once(self):
        return (len(set(list(self.text))) < len(self.text))

@efd.put('{backticked_word} : ` \\w+ `')
def _(de, chars):
    word_chars = chars[1:-1]
    return ES_UnicodeCodePoints(word_chars)

@efd.put('{EXPR} : the source text matched by {PROD_REF}')
def _(de, prod_ref):
    pnode = de.exec(prod_ref, ParseNode)
    return ES_UnicodeCodePoints(pnode.text())

@efd.put('{EXPR} : the number of code points in {PROD_REF}') # SPEC BUG: the number of code points in the source text matched by {PROD_REF}
def _(de, prod_ref):
    pnode = de.exec(prod_ref, ParseNode)
    return ES_Mathnum(len(pnode.text()))

@efd.put('{EX} : the number of code points in {PROD_REF}, excluding all occurrences of {nonterminal}')
def _(de, prod_ref, nont):
    pnode = de.exec(prod_ref, ParseNode)
    assert nont.source_text() == '|NumericLiteralSeparator|'
    return ES_Mathnum(len(pnode.text().replace('_', '')))

@efd.put('{CONDITION_1} : {PP_NAMED_OPERATION_INVOCATION} contains any code points other than {backticked_word}, {backticked_word}, {backticked_word}, {backticked_word}, {backticked_word}, or {backticked_word}, or if it contains the same code point more than once')
def _(de, noi, *backticked_words):
    noi_val = de.exec(noi, ES_UnicodeCodePoints)
    allowed_code_points = []
    for btw in backticked_words:
        cps = de.exec(btw, ES_UnicodeCodePoints)
        assert cps.number_of_code_points() == 1
        [cp] = cps.code_points()
        allowed_code_points.append(cp)
    return (
        noi_val.contains_any_code_points_other_than(allowed_code_points)
        or
        noi_val.contains_the_same_code_point_more_than_once()
    )

@efd.put('{CONDITION_1} : {PP_NAMED_OPERATION_INVOCATION} contains {backticked_word}')
def _(de, noi, backticked_word):
    noi_val = de.exec(noi, ES_UnicodeCodePoints)
    cps = de.exec(backticked_word, ES_UnicodeCodePoints)
    assert cps.number_of_code_points() == 1
    [cp] = cps.code_points()
    return noi_val.contains_code_point(cp)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

# 8.4.1 Static Semantics: Contains

@efd.put('{CONDITION_1} : {LOCAL_REF} Contains {G_SYM}') # spec bug: should say "is *true*"
def _(de, local_ref, g_sym):
    boolean_value = execute_sdo_invocation(de, 'Contains', local_ref, [g_sym])
    assert isinstance(boolean_value, EL_Boolean)
    return boolean_value.b

@efd.put('{CONDITION_1} : {LOCAL_REF} Contains {G_SYM} is {BOOL_LITERAL}') # This should be decomposed
def _(de, local_ref, g_sym, boolean_literal):
    contains_boolean = execute_sdo_invocation(de, 'Contains', local_ref, [g_sym])
    test_boolean = de.exec(boolean_literal, EL_Boolean)
    return same_value(contains_boolean, test_boolean)

@efd.put('{NAMED_OPERATION_INVOCATION} : {LOCAL_REF} Contains {var}')
@efd.put('{NAMED_OPERATION_INVOCATION} : {LOCAL_REF} Contains {nonterminal}')
def _(de, local_ref, sym):
    return execute_sdo_invocation(de, 'Contains', local_ref, [sym])

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

# 11.1.6 Static Semantics: ParseText ( sourceText, goalSymbol )

@efd.put('{COMMAND} : Attempt to parse {var} using {var} as the goal symbol, and analyse the parse result for any early error conditions. Parsing and early error detection may be interleaved in an implementation-defined manner.')
def _(de, subject_var, goal_var):
    subject = de.exec(subject_var, ES_UnicodeCodePoints)
    goal_sym = de.exec(goal_var, ES_NonterminalSymbol)
    frame = de.curr_frame()
    try:
        frame.kludge_node = parse(subject.text, goal_sym.name)
    except ParseError as e:
        frame.kludge_node = None
        frame.kludge_errors = [e]
        return
    frame.kludge_errors = de.get_early_errors_in(frame.kludge_node)

@efd.put('{CONDITION_1} : the parse succeeded and no early errors were found')
def _(de):
    frame = de.curr_frame()
    return (
        frame.kludge_node is not None
        and
        frame.kludge_errors == []
    )

@efd.put('{EXPR} : the Parse Node (an instance of {var}) at the root of the parse tree resulting from the parse')
def _(de, var):
    gsym = de.exec(var, ES_GrammarSymbol)
    frame = de.curr_frame()
    assert (
        frame.kludge_node is not None
        and
        frame.kludge_errors == []
    )
    return frame.kludge_node

@efd.put('{EXPR} : a List of one or more {ERROR_TYPE} objects representing the parsing errors and/or early errors. If more than one parsing error or early error is present, the number and ordering of error objects in the list is implementation-defined, but at least one must be present')
def _(de, error_type):
    assert error_type.source_text() == '*SyntaxError*'
    frame = de.curr_frame()
    assert frame.kludge_errors
    objects = [
        EL_Object([])
        # ee.kind, ee.location, ee.condition
        for ee in frame.kludge_errors
    ]
    return ES_List(objects)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

# 11.2 Types of Source Code

@efd.put('{CONDITION_1} : the source code containing {G_SYM} is eval code that is being processed by a direct eval')
def _(de, gsym):
    return False # BUG

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

# 11.2.2 Strict Mode Code

@efd.put('{CONDITION_1} : the code that matches {PROD_REF} is contained in strict mode code')
@efd.put('{CONDITION_1} : the code matched by {PROD_REF} is contained in strict mode code')
@efd.put('{CONDITION_1} : the source code matching {PROD_REF} is strict mode code')
@efd.put('{CONDITION_1} : {LOCAL_REF} is contained in strict mode code')
@efd.put('{CONDITION_1} : {PROD_REF} is contained in strict mode code')
def _(de, local_ref):
    pnode = de.exec(local_ref, ParseNode)
    return is_strict(pnode)

@efd.put('{CONDITION_1} : the Directive Prologue of {PROD_REF} contains a Use Strict Directive')
def _(de, prod_ref):
    pnode = de.exec(prod_ref, ParseNode)
    return begins_with_a_DP_that_contains_a_USD(pnode)

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
    assert isinstance(list_node, ParseNode)
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

# 12 ECMAScript Language: Lexical Grammar

#> The source text of an ECMAScript Script or Module
#> is first converted into a sequence of input elements,
#> which are tokens, line terminators, comments, or white space.
#> The source text is scanned from left to right,
#> repeatedly taking the longest possible sequence of code points
#> as the next input element.

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

# 13.2.5.1 Static Semantics: Early Errors

@efd.put('{CONDITION_1} : at least two of those entries were obtained from productions of the form {h_emu_grammar}')
def _(de, h_emu_grammar):
    # This one's weird, because it's asking "after the fact"
    # about how the results of PropertyNameList were obtained.
    return False # TODO

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

# 22.2 RegExp (Regular Expression) Objects

@efd.put('{CONDITION_1} : {LOCAL_REF} contains multiple {nonterminal}s whose enclosed {nonterminal}s have the same {cap_word}')
def _(de, local_ref, nonta, nontb, cap_word):
    pattern = de.exec(local_ref, ParseNode)
    nta = nt_name_from_nonterminal_node(nonta)
    ntb = nt_name_from_nonterminal_node(nontb)
    something = []
    for node in pattern.preorder_traverse():
        if node.symbol == nta:
            print('2029:', node.source_text())
            something.append(node.source_text())
    if len(something) <= 1:
        return False
    assert NYI

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

# 25.5.1 JSON.parse

@efd.put('{CONDITION_1} : {PROD_REF} is contained within a {nonterminal} that is being parsed for JSON.parse (see step {h_emu_xref} of {h_emu_xref})')
def _(de, prod_ref, nont, step_xref, alg_xref):
    node = de.exec(prod_ref, ParseNode)
    container_nt = nt_name_from_nonterminal_node(nont)
    assert container_nt == 'Script'
    if node.root().symbol != container_nt: return False
    # TODO: detect whether the Script is being parsed for JSON.parse
    return False

# vim: sw=4 ts=4 expandtab
