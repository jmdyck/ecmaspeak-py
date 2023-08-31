#!/usr/bin/python3

# ecmaspeak-py/Pseudocode_Parser.py:
# Parse various flavors of ECMASpeak pseudocode.
#
# Copyright (C) 2018  J. Michael Dyck <jmdyck@ibiblio.org>

import sys, collections, pdb, math, functools, os, re

from LR_Parser import LR_Parser, ParsingError, TooManyHeadsError
# import Earley
import shared
from shared import SpecNode

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

class Tokenizer:
    def __init__(self, tokenizer_definition_string):
        self.prod_for_pi = {}
        patterns = []
        i = 0
        for line in tokenizer_definition_string.split('\n'):
            line = line.lstrip()
            if line == '':
                # blank line
                pass
            elif line.startswith('#'):
                # comment
                pass
            else:
                mo = re.fullmatch(r'({\w+}) +: +([^ ].*)', line)
                assert mo
                (lhs, rhs) = mo.groups()
                i += 1
                pi = f"p{i}"
                self.prod_for_pi[pi] = Production(True, lhs, rhs)
                patterns.append(f"(?P<{pi}> {rhs} )")
        pattern = '\n| '.join(patterns)
        self.reo = re.compile(pattern, re.VERBOSE)

    def tokenize(self, s, start_posn, end_posn, generate_dent_tokens, initial_indentation):
        prev_indentation = initial_indentation
        posn = start_posn
        while True:
            mo = self.reo.match(s, posn, end_posn)
            if mo is None:
                shared.stderr(
                    f"\nTokenization error at: {s[posn:min(posn+20,end_posn)]}...\n",
                    shared.source_line_with_caret_marking_column(tok_s_posn)
                )
                assert 0
            pi = mo.lastgroup
            text = mo.group(pi)
            (tok_s_posn, tok_e_posn) = mo.span(pi)

            # XXX The sub-pattern associated with this group
            # might have a capturing subgroup
            # (whose value might be more useful than the group's),
            # but accessing it would be tricky,
            # because it doesn't have a name,
            # and we don't know its number in the overall pattern.
            # Either would take a bit of work.

            prod = self.prod_for_pi[pi]

            if generate_dent_tokens and prod.lhs_s == '{nlai}':
                this_indentation = len(text) - 1 # subtract 1 for the \n

                change_in_indentation = this_indentation - prev_indentation
                indent_unit = 2
                assert change_in_indentation % indent_unit == 0
                n_dents = change_in_indentation // indent_unit
                if n_dents > 0:
                    dent_prod = indent_prod
                elif n_dents < 0:
                    dent_prod = outdent_prod
                else:
                    dent_prod = None
                for i in range(abs(n_dents)):
                    yield (dent_prod, tok_s_posn, tok_s_posn, '')

                prev_indentation = this_indentation

            yield (prod, tok_s_posn, tok_e_posn, text)

            if prod.lhs_s == '{_eos_}': break

            posn = tok_e_posn

class Production:
    def __init__(self, is_token_prod, lhs_s, rhs_s):
        self.is_token_prod = is_token_prod
        self.lhs_s = lhs_s
        self.rhs_s = rhs_s

        # In a GLR parse, there can be lots of reductions
        # that ultimately don't appear in the final parse tree.
        self.n_reductions = 0
        self.n_delivered_instances = 0

    def __str__(self):
        return self.lhs_s + ' : ' + self.rhs_s

indent_prod  = Production(True, '{_indent_}', '')
outdent_prod = Production(True, '{_outdent_}', '')

# This is for tokenizing the pseudocode text.
# But before that we have to tokenize the pseudocode-grammars, see below at
# reo_for_rhs_piece_in_pseudocode_grammar.
tokenizer_for_pseudocode = Tokenizer(r'''
    {_eos_}          : $

    # tokens that begin with whitespace:
    {nlai}           : \n \x20*
    {space}          : \x20

    # tokens that begin with left-angle-bracket:
    {h_a}            : <a \x20 [^<>]+> ( [^<>]+ | <code> [^<>]+ </code> ) </a> 
    {h_code_quote}   : <code>"%<var>(NativeError|TypedArray)</var>Prototype%"</code>
    {h_code_quote}   : <code>"%<var>(NativeError|TypedArray)</var>.prototype%"</code>
    {h_code_quote}   : <code>"%(NativeError|TypedArray)Prototype%"</code>
    {h_figure}       : <figure> (.|\n)+? </figure>
    {h_pre_code}     : <pre><code \x20 class="javascript"> ([^<>]+) </code></pre>
    {h_emu_grammar}  : < emu-grammar > .+? </ emu-grammar >
    {h_emu_note}     : < emu-note > (.|\n)+? </ emu-note >
    {h_emu_xref}     : < emu-xref (\x20 \w+ (= " [^"]+ ")? )* > [^<>]* < / emu-xref >
    {h_emu_alg}      : < emu-alg > (.|\n)+? < / emu-alg >
    {h_emu_not_ref_Record}        : < emu-not-ref > Record < / emu-not-ref >
    {h_emu_not_ref_Property_name} : < emu-not-ref > Property \x20 name < / emu-not-ref >
    {h_emu_not_ref_property_name} : < emu-not-ref > property \x20 name < / emu-not-ref >
    {h_emu_not_ref_substring}     : < emu-not-ref > substring < / emu-not-ref >
    {h_sub_fancy_f}   : < sub > \U0001d53d < / sub >
    {h_sub_fancy_r}   : < sub > \u211d < / sub >
    {h_sub_fancy_z}   : < sub > \u2124 < / sub >
    {h_emu_meta_start} : < emu-meta \x20 [\w-]+ = " [^"]+ ">
    {h_emu_meta_end}   : < / emu-meta >
    {h_start_tag}    : < [\w-]+ (\x20 \w+ (= " [^"]+ ")? )* >
    {h_end_tag}      : </ [\w-]+ >

    # tokens that begin with '*':
    {starred_int_lit}       : \* [+-] 0 \*
    {starred_int_lit}       : \* [+-]? \d+ \*
    {starred_bigint_lit}    : \* [01] n \*
    {starred_neg_infinity_lit} : \*  - ∞ \*
    {starred_pos_infinity_lit} : \* \+ ∞ \*
    {starred_nan_lit}       : \* NaN \*
    {starred_word}          : \* [A-Za-z]+ \*
    {starred_str}           : \* " ( [^"*] | \\ \* )* " \*

    # tokens that begin with '[':
    {dsb_word}         : \[\[ [A-Z][A-Za-z0-9]* \]\]
    {dsb_percent_word} : \[\[ % [A-Z][A-Za-z]* (\. \w+)* % \]\]
    {step_attribute}   : \[ [\w-]+ = "[^"]+" \]
    {punct}            : \[
    {punct}            : \]

    # tokens that begin with backtick:
    {code_point_lit}  : ` [^`]+ ` \x20 U \+ [0-9A-F]{4} \x20 \( [A-Z -]+ \)
    {backticked_str}  : ` " [^"`]* " `
    {backticked_word} : ` \w+ `
    {backticked_oth}  : ` [^`]+ `

    # tokens that begin with tilde:
    {tilded_word}    : ~ [-a-z0-9+]+ ~

    # tokens that begin with other distinctive characters:
    {char_ref}       : & [a-z]+ ;
    {atat_word}      : @@ \w+ \b
    {percent_word}   : % \w+ (\. \w+)* %
    {nonterminal}    : \| [A-Za-z][A-Za-z0-9]* \?? (\[ .+? \])? \|
    {var}            : \b _ [A-Za-z][A-Za-z0-9]* _ \b

    {var} : \b _i_th \b
    # for branches based before the merge of PR #1566

    # tokens that begin with a digit:
    {code_unit_lit}  : \b 0x [0-9A-F]{4} \x20 \( [A-Z -]+ \)
    {hex_int_lit}    : \b 0x [0-9A-F]{2,6} \b
    {dec_int_lit}    : \b [0-9]+ (?![0-9A-Za-z])
        # We can't end with \b,
        # because there's an occurrence of 3π,
        # and π is a word-character, so \b doesn't match after the '3'.
    {wordish}        : \b 20th \b

    # single-character symbols:
    {punct}          : [-()=/+,.:?!;{}*@>]
    {nonascii}       : [ « » × π “ ” ∞ ≠ ≤ ≥ ]

    # tokens that begin with a letter:

    {the_field_names_are_the_names_listed_etc} : The \x20 field \x20 names \x20 are \x20 the \x20 names \x20 listed \x20 .+\.

    {code_point_lit} : \b U \+ [0-9A-F]{4} \x20 \( [A-Z -]+ \)
    {code_unit_lit}  : the \x20 code \x20 unit \x20 0x [0-9A-F]{4} \x20 \( [A-Z -]+ \)

    {note}           : \b NOTE: \x20 .+

    {wordish}        : \b (don't | doesn't | We've) \b
    {wordish}        : 's \b
    {wordish}        : \b General_Category \b

    {special_word}   : \b ( Type | Function | Realm | ScriptOrModule | LexicalEnvironment | VariableEnvironment | Generator | PrivateEnvironment ) \b
    {cap_word}       : \b [A-Z][A-Za-z0-9]* \b
    {low_word}       : \b [a-z][A-Za-z0-9]* \b

    {fancy_f}        : \U0001d53d
    {fancy_r}        : \u211d
    {fancy_z}        : \u2124

''')

tokenizer_for_RHSs_in_pseudocode_grammars = Tokenizer(r'''
''')

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

class Pseudocode_Parser:
    def __init__(self, file_base):
        self.file_base = file_base

        grammar_string = open(f"{os.path.dirname(__file__)}/{file_base}.grammar", 'r', encoding='utf-8').read()

        self.productions = convert_grammar_string_to_productions(grammar_string)
        simple_prods = [
            (prod.lhs_s, prod.rhs_pieces)
            for prod in self.productions
        ]
        # LR
        self.lr_parser = LR_Parser('SLR(1)', simple_prods, 'silent')

        #   # Earley (attempt, doesn't work)
        #   self.eparser = Earley.Parser(simple_prods, '*EOI*')

        if shared.g_outdir:
            self.f_errors = shared.open_for_output(file_base + '_errors')
            self.f_ambig = shared.open_for_output(file_base + '_ambig')
            self.f_parsed = shared.open_for_output(file_base + '_parsed')
        else:
            # testing
            self.f_ambig = sys.stdout

        self.error_count = 0
        self.group_errors_by_expectation = True

        if self.group_errors_by_expectation:
            self.error_posns = collections.defaultdict(list)

    def parse_and_handle_errors(self, start_posn, end_posn, goal):

        entry_lhs = '{_' + goal.lower() + '_}'
        entry_rhs = ''
        entry_prod = Production(True, entry_lhs, entry_rhs)
        entry_token = (entry_prod, start_posn, start_posn, '')

        # hm
        # Find the start of 'this line'
        # (the line that contains start_posn)
        for posn in range(start_posn, -1, -1):
            if posn == 0 or shared.spec_text[posn-1] == '\n':
                line_start_posn = posn
                break
        else:
            assert 0
        # And then find the end of this line's indentation
        for posn in range(line_start_posn, start_posn+1):
            if shared.spec_text[posn] != ' ':
                line_indent_end_posn = posn
                break
        else:
            assert 0
        #
        this_line_indentation = line_indent_end_posn - line_start_posn

        token_generator = tokenizer_for_pseudocode.tokenize(
            shared.spec_text,
            start_posn,
            end_posn,
            True,
            this_line_indentation
        )

        tokens = [entry_token] + [ token_info for token_info in token_generator ]

        def matcher_for_gparse(curr_tind, terminals):
            assert curr_tind < len(tokens)
            (tok_prod, tok_s_posn, tok_e_posn, tok_text) = tokens[curr_tind]

            matching_terminals = []
            for terminal in terminals:
                    
                assert isinstance(terminal, str)

                match_token = False

                if terminal.startswith('{') and terminal.endswith('}'):
                    if tok_prod.lhs_s == terminal:
                        if terminal in ['{nlai}', '{_indent_}', '{_outdent_}']:
                            match_token = None
                        else:
                            match_token = ANode(tok_prod, [tok_text], tok_s_posn, tok_e_posn)
                else:
                    if terminal == 'an?':
                        if tok_text in ['a', 'an']:
                            match_token = None
                    else:
                        if tok_text == terminal:
                            match_token = None

                if match_token is not False:
                    matching_terminals.append( (terminal, curr_tind+1, match_token) )

            return matching_terminals

        def reducer(pi, reductands, s_tind, e_tind):
            prod = self.productions[pi]
            prod.n_reductions += 1
            assert len(reductands) == len(prod.rhs_pieces)

            if prod.lhs_s.startswith('{_'):
                # We're not interested in the details.
                return None

            node_children = []
            for red in reductands:
                if red is None:
                    # rhs_piece is a regex with no capturing group
                    # or is an uninteresting nonterminal
                    continue
                if red.prod.lhs_s == '{space}': continue
                node_children.append(red)

            (_, s_posn, _, _) = tokens[s_tind]
            (_, e_posn, _, _) = tokens[e_tind]
            node = ANode(prod, node_children, s_posn, e_posn)
            return node

        try:
            results = self.lr_parser.gparse(matcher_for_gparse, reducer, 0)

        except ParsingError as e:
            self.error_count += 1
            (_, tok_s_posn, _, _) = tokens[e.posn]
            if self.group_errors_by_expectation:
                self.error_posns[tuple(e.expecting)].append(tok_s_posn)
            else:
                print(
                    '\n'
                    +
                    shared.source_line_with_caret_marking_column(tok_s_posn)
                    +
                    '\n'
                    +
                    "Expecting: "
                    +
                    ' '.join(e.expecting),
                    file=self.f_errors
                )
            print('(Error)', file=self.f_parsed)
            return None

        except TooManyHeadsError as e:
            (_, tok_s_posn, _, _) = tokens[e.posn]
            print(shared.source_line_with_caret_marking_column(tok_s_posn))
            raise

        if len(results) != 1:
            print('-------------------------------', file=self.f_ambig)
            for result in results:
                result.printTree(self.f_ambig)

        result = results[0]

        result.set_parent_links()

        def count(node):
            if isinstance(node, str): return
            assert isinstance(node, ANode)
            if not hasattr(node.prod, 'n_delivered_instances'): return
            node.prod.n_delivered_instances += 1
            for child in node.children:
                count(child)

        count(result)

        [entry_node, goal_node] = result.children
        assert entry_node.prod is entry_prod
        assert goal_node.prod.lhs_s == '{' + goal + '}'

        goal_node.printTree(self.f_parsed)

        return goal_node

    def report(self):
        report_file_base = self.file_base + '_prod_counts'
        shared.stderr(f"generating new {report_file_base} ...")

        if self.group_errors_by_expectation:
            # This approach is better when I'm developing a grammar,
            # as it tends to group similar cases.

            def err(x): print(x, file=self.f_errors)

            err("%d parsing errors:" % self.error_count)
            err('')
            for (expecting, posns) in sorted(self.error_posns.items()):
                # err('')
                err('X'*80)
                # err('')
                err("Expecting:")
                for e in expecting:
                    err("    %r"  % e)
                for posn in posns:
                    err(shared.source_line_with_caret_marking_column(math.ceil(posn)))

        f = shared.open_for_output(report_file_base)
        for prod in self.productions:
            print("%5d %s" % (prod.n_delivered_instances, prod), file=f)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

nt_pattern = r'\{[A-Z_][A-Z_0-9]*\}'

def convert_grammar_string_to_productions(grammar_string):

    lhs_set = set()
    productions = []
    current_lhs = None
    for line in grammar_string.split('\n'):
        if line == '':
            # blank line
            continue
        elif re.match(r'^ *#', line):
            # comment line
            continue
        elif not line.startswith(' '):
            # lhs
            mo = re.match(f'^({nt_pattern}) :$', line)
            assert mo, line
            current_lhs = mo.group(1)
            assert current_lhs not in lhs_set
            lhs_set.add(current_lhs)
        else:
            # rhs
            rhs = line.lstrip()
            prod = Production(False, current_lhs, rhs)

            prod.rhs_pieces = []
            posn = 0
            while True:
                if posn == len(rhs):
                    break
                mo = reo_for_rhs_piece_in_pseudocode_grammar.match(rhs, posn)
                if mo:
                    t_end_posn = mo.end()
                    # shared.stderr(rhs[posn:t_end_posn])
                    text = rhs[posn:t_end_posn]
                    if text.startswith(r'\u'): text = chr(int(text[2:], 16))
                    prod.rhs_pieces.append(text)
                    posn = t_end_posn
                else:
                    print('in one of the grammars for pseudocode:')
                    caret_line = '-' * posn + '^'
                    x = rhs + '\n' + caret_line
                    print( '\n' + x + '\n', file=sys.stderr)
                    sys.exit(1)

            if '{EPSILON}' in prod.rhs_pieces:
                assert prod.rhs_pieces == ['{EPSILON}']
                prod.rhs_pieces = []

            productions.append(prod)

    # Now that we have all productions,
    # do a consistency check.
    for production in productions:
        for r_item in production.rhs_pieces:
            if re.match(r'^%s$' % nt_pattern, r_item):
                assert r_item in lhs_set, ("%s looks like a nonterminal but doesn't appear on a LHS" % r_item)

    return productions

reo_for_rhs_piece_in_pseudocode_grammar = re.compile(r'''(?x)
      \x20

    | { _? [A-Z] [A-Z_0-9]* }
    | { _? [a-z] \w* }

    | < /? (b|br|i|ins|p|sub|sup|var)>

    | \* [+-] 0 \*
    | \* [A-Za-z]+ \*
    | \* " [^"]? " \*

    | ` [^`]+ `

    | & [a-z]+ ;
    | \| [A-Za-z][A-Za-z0-9]* \|
    | _captures_
    | _endIndex_
    | _input_
    | _startIndex_

    | \b [0-9]+ (?![0-9A-Za-z])

    | [-!()*+,./:;=>?{}]
    | [ « » × π “ ” ∞ ≠ ≤ ≥ ]
    | \[
    | \]

    | \b an\?
    | \b (doesn't | We've) \b
    | \b 20th \b
    | \b   [A-Za-z][A-Za-z0-9]* \b
    | \b General_Category \b
    | 's \b
''')

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

class ANode(SpecNode):
    def __init__(self, prod, children, start_posn, end_posn):
        assert isinstance(prod, Production) or prod is None
        assert isinstance(children, list) or children is None
        # The 'None's come from Header::__init__ in static_type_analysis.py
        assert isinstance(start_posn, int)
        assert isinstance(end_posn, int)

        SpecNode.__init__(self, start_posn, end_posn)

        self.prod = prod
        self.children = children

    def set_parent_links(self):
        if self.children:
            for child in self.children:
                if isinstance(child, ANode):
                    child.parent = self
                    child.set_parent_links()

    def __repr__(self):
        t = self.source_text()
        if len(t) <= 70:
            s = t
        else:
            s = t[0:67] + '...'
        return f'ANode(prod="{self.prod}", {len(self.children)} children, source_text={s!r}'

    def closest_containing(self, lhs_s):
        for ancestor in self.each_ancestor_or_self():
            if ancestor.prod.lhs_s == lhs_s:
                return ancestor
        return None

    def each_ancestor_or_self(self):
        ancestor = self
        while ancestor is not None:
            yield ancestor
            ancestor = ancestor.parent

    def each_descendant_or_self(self):
        yield self
        yield from self.each_descendant()

    def each_descendant(self):
        for child in self.children:
            if isinstance(child, ANode):
                yield child
                yield from child.each_descendant()

    def printTree(self, f=sys.stdout, level=0):
        indentation = '  '*level
        if self.children == []:
            print(indentation + '(' + str(self.prod) + ')', file=f)
        else:
            print(indentation + '(' + str(self.prod), file=f)
            for child in self.children:
                if isinstance(child, str):
                    print(indentation + '  ' + literalize(child), file=f)
                else:
                    child.printTree(f, level+1)
            print(indentation + ')', file=f)

    def is_a(self, lhs_s):
        node = self
        while True:
            if node.prod.lhs_s == lhs_s:
                return node
            elif len(node.children) == 1:
                [child] = node.children
                if isinstance(child, ANode):
                    node = child
                else:
                    return None
            else:
                return None

def literalize(s):
    return (
        '"'
        + s
            .replace('\n', r'\n')
            .replace('"', '""')
        + '"'
    )

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

# vim: sw=4 ts=4 expandtab
