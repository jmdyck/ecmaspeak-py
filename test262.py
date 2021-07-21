#!/usr/bin/python3

# ecmaspeak-py/test262.py:
# Test using the 'test262' repo.
#
# Copyright (C) 2021  J. Michael Dyck <jmdyck@ibiblio.org>

import sys, os, re

from shared import stderr

root_test_dirpath = "../test262/test"

NYI = 0 # Not Yet Implemented

n_test_files = 0
n_test_runs = 0

def main():
    if len(sys.argv) == 1:
        stderr(f"usage: {sys.argv[0]} [ --all | --all-dir=<dir> | <file> ... ]")
    elif sys.argv[1] == '--all':
        test_all()
    elif mo := re.fullmatch(r'--all-dir=(\S+)', sys.argv[1]):
        test_dirname = mo.group(1)
        test_all_in_dir(test_dirname)
    else:
        for test_file_relpath in sys.argv[1:]:
            test_one(test_file_relpath)
    stderr(f"{n_test_files} tests")
    stderr(f"{n_test_runs} test runs")

def test_all():
    test_all_in_dir('.')

def test_all_in_dir(dir_relpath):
    # print(dir_relpath + ' ...')
    dir_abspath = root_test_dirpath + '/' + dir_relpath
    assert os.path.isdir(dir_abspath)
    entries = []
    for entry in os.scandir(dir_abspath):
        if entry.is_symlink():
            assert 0
        elif entry.is_file():
            if re.fullmatch('\.[a-zA-Z0-9_.-]+\.(js|json)\.swp', entry.name):
                # vim swap file, ignore it.
                continue
            assert re.fullmatch('[a-zA-Z0-9_.-]+\.(js|json)', entry.name), entry.name
            if '_FIXTURE' in entry.name:
                # involved in a test, but not itself a test
                continue
            entries.append((0, entry.name))
        elif entry.is_dir():
            assert re.fullmatch('[a-zA-Z0-9_.-]+', entry.name), entry.name
            entries.append((1, entry.name))
        else:
            assert 0

    entries.sort()

    for (is_dir, entry_name) in entries:
        relpath = dir_relpath + '/' + entry_name
        if is_dir:
            test_all_in_dir(relpath)
        else:
            test_one(relpath)

def test_one(file_relpath):
    file_abspath = root_test_dirpath + '/' + file_relpath
    # stderr(file_abspath)
    assert os.path.isfile(file_abspath)
    file_text = open(file_abspath, 'r').read()
    # print(file_text[0:30])

    #> A test file has three sections: Copyright, Frontmatter, and Body.

    [mo1] = [* re.finditer(r'\n/\*---\n', file_text) ]
    [mo2] = [* re.finditer(r'\n---\*/\n', file_text) ]

    copyright   = file_text[0        :mo1.start()]
    frontmatter = file_text[mo1.end():mo2.start()]
    body        = file_text[mo2.end():]

    # copyright
    if all(
        line.startswith('// ') or line == ''
        for line in copyright.split('\n')
    ):
        # The expected format.
        pass

    elif file_relpath.startswith(("./language/comments/hashbang/","language/comments/hashbang/")):
        # For these, the hashbang has to be at the start of the file.
        # So you get at least one non-comment line before the comment lines.
        pass

    else:
        assert 0, file_relpath

    # frontmatter
    try:
        d = parse_frontmatter(frontmatter)
    except AssertionError:
        print(f"... failed to parse frontmatter in {file_relpath}")
        return

    assert isinstance(d, dict)
    keys_here = d.keys()
    all_valid_keys = {
        'description',
        'esid',
        'info',
        'negative',
        'includes',
        'author',
        'flags',
        'features',
        'es5id',
        'es6id',
        'locale', # not described in CONTRIBUTING.md, see issue #3015
    }
    invalid_keys = keys_here - all_valid_keys
    for key in sorted(invalid_keys):
        print(f"unexpected key {key!r} in {file_relpath}")

    def check(dic, key, value_class):
        if key in dic:
            assert isinstance(dic[key], value_class)

    assert 'description' in d
    check(d, 'description', str)
    check(d, 'esid', str)
    check(d, 'info', str)

    if 'negative' in d:
        neg = d['negative']
        assert isinstance(neg, dict)
        assert neg.keys() == {'type', 'phase'}
        assert neg['type'] in ['RangeError', 'ReferenceError', 'SyntaxError', 'Test262Error', 'TypeError']
        assert neg['phase'] in ['parse', 'resolution', 'runtime']

    if 'includes' in d:
        incs = d['includes']
        assert isinstance(incs, list)
        assert len(incs) > 0
        for inc in incs:
            assert isinstance(inc, str)
            assert re.fullmatch(r'[\w-]+\.js', inc), inc

    check(d, 'author', str)

    if 'flags' in d:
        flags = d['flags']
        assert isinstance(flags, list)
        assert len(flags) > 0
        flagset = set(flags)
        assert len(flagset) == len(flags) # no duplicates
        valid_flags = {
            'onlyStrict',
            'noStrict',
            'module',
            'raw',
            'async',
            'generated',
            'CanBlockIsFalse',
            'CanBlockIsTrue',
            'non-deterministic', # not described in CONTRIBUTING.md, see issue #3015
        }
        invalid_flags = flagset - valid_flags
        for flag in sorted(invalid_flags):
            print(f"invalid flag {flag!r} in {file_relpath}")
        assert (
            ('onlyStrict' in flagset)
            +
            ('noStrict' in flagset)
            +
            ('raw' in flagset)
        ) <= 1
    else:
        flagset = set()

    if 'features' in d:
        features = d['features']
        assert isinstance(features, list)
        assert len(features) > 0
        assert len(set(features)) == len(features) # no duplicates
        for feature in features:
            # assert feature in [those declared in features.txt]
            pass

    check(d, 'es5id', str)
    check(d, 'es6id', str)

    # ---------------------------------------

    if (
        'onlyStrict' in flagset
        or 'noStrict' in flagset
        or 'raw' in flagset
    ):
        n_runs_for_this_test = 1
    else:
        n_runs_for_this_test = 2

    # ---------------------------------------

    global n_test_files
    n_test_files += 1

    global n_test_runs
    n_test_runs += n_runs_for_this_test

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def parse_frontmatter(frontmatter):
    line_posns = [
        (mo.start(1), mo.end(1), mo.end(2))
        for mo in re.finditer(r'(?m)^( *)(.*)$', frontmatter)
    ]
    # for (a,b,c) in line_posns: print(b-a, repr(frontmatter[b:c]))

    if 0:
        for (a,b,c) in line_posns:
            if re.compile(r' $').search(frontmatter, b, c):
                print(frontmatter[a:c]+'$')
        # 450 hits, so might as well accept it

    def yaml_parse_block_collection(start_line_i, end_line_i):

        # Examine the first line
        (a, b, c) = line_posns[start_line_i]
        first_indent = b-a
        assert b < c
        if frontmatter[b] == '-':
            kind_of_collection = 'sequence'
            collection = []
        elif ': ' in frontmatter[b:c]:
            kind_of_collection = 'mapping'
            collection = {}
        else:
            print()
            print("Expected a collection in block notation, but got a scalar in flow notation starting on the line after the key?")
            print(f"    {frontmatter[b:c]}")
            assert 0

        # --------

        # Find all the lines (in the given range)
        # that have the same indentation as the first.
        # Each of these is the start of (and possibly the whole of)
        # an element of the collection.

        child_start_line_indexes = []
        for i in range(start_line_i, end_line_i):
            (a, b, c) = line_posns[i]
            assert a <= b <= c
            if b == c:
                # A line with nothing after (optional) indentation.
                # Visually empty line, has no effect on partition.
                continue

            this_indent = b - a
            assert this_indent >= first_indent
            if this_indent == first_indent:
                child_start_line_indexes.append(i)

        # --------

        # Examine (the lines that define) each element of the collection.

        for (s_line_i, e_line_i) in zip(child_start_line_indexes, child_start_line_indexes[1:] + [end_line_i]):
            # print('---')
            # for (a,b,c) in line_posns[s_line_i: e_line_i]: print(b-a, repr(frontmatter[b:c]))

            # Trim empty lines from end
            while True:
                (a,b,c) = line_posns[e_line_i-1]
                if b == c:
                    e_line_i -= 1
                else:
                    break

            n_lines = e_line_i - s_line_i
            assert n_lines >= 1

            (a,b,c) = line_posns[s_line_i]
            if kind_of_collection == 'sequence':
                assert n_lines == 1
                mo = re.compile(r'- (.+)').match(frontmatter, b, c)
                assert mo
                value = mo.group(1)
                assert value[0] not in [' ', '[', '{']
                collection.append(value)

            else:
                mo = re.compile(r'(\w+):(.*)').match(frontmatter, b, c)
                assert mo
                key = mo.group(1)
                assert key not in collection
                rest = mo.group(2)

                if n_lines == 1:
                    # all info on this line, in {rest}
                    if rest.startswith(' {'):
                        assert 0
                    elif rest.startswith(' ['):
                        assert rest.endswith(']')
                        # if re.search(',[^ ]', rest): print(rest)
                        value = re.split(', *', rest[2:-1])
                    elif rest.startswith(' '):
                        value = rest[1:]
                    else:
                        assert 0

                elif rest == ' |':
                    # Scalar content, written in block notation, using literal style.
                    # (newlines are preserved)
                    # (except, in many cases, newlines shouldn't be preserved)
                    value = frontmatter[
                        line_posns[s_line_i+1][0]
                        :
                        line_posns[e_line_i-1][2]
                    ]
                    # for (a,b,c) in line_posns[s_line_i: e_line_i]: print(repr(frontmatter[a:c]))

                elif rest == ' >':
                    # Scalar content, written in block notation, using folded style.
                    # (Each line break is folded to a space
                    # unless it ends an empty or a more-indented line.)
                    value = frontmatter[
                        line_posns[s_line_i+1][0]
                        :
                        line_posns[e_line_i-1][2]
                    ]

                elif rest == '' or rest.isspace():
                    # Collection content, written in block notation
                    value = yaml_parse_block_collection(s_line_i+1, e_line_i)

                else:
                    text = frontmatter[
                        mo.start(2)
                        :
                        line_posns[e_line_i-1][2]
                    ]
                    print()
                    print(f"Value for key {key!r} is a multi-line scalar in flow notation:")
                    print(f"    {text!r}")
                    assert 0

                collection[key] = value

        return collection

    return yaml_parse_block_collection(0, len(line_posns))

main()

# vim: sw=4 ts=4 expandtab
