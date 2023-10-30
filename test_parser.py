#!/usr/bin/python3

# ecmaspeak-py/test_parser.py:
# Test es_parser using the 'test262-parser-tests' repo.
# 
# Copyright (C) 2018  J. Michael Dyck <jmdyck@ibiblio.org>

# example use:
# test_parser.py --all && car _test_parser/{fail,early,pass,pass-explicit}_output
# ^ takes about 7 minutes
# test_parser.py --all-dir=fail && car _test_parser/fail_output

# You may need to `export PYTHONIOENCODING=utf-8` before running this script.

import sys, os, re, contextlib, time

import shared

g_outdir = sys.argv[1]
shared.register_output_dir(g_outdir)
shared.spec.restore()

import es_parser
import misc
import pseudocode_semantics

root_test_dirpath = "../test262-parser-tests"

def main():
    if len(sys.argv) == 1:
        print(f"usage: {sys.argv[0]} <pickle-dir> [ --all | --all-dir=<dir> | <filepath> ... ]")
    elif sys.argv[2] == '--all':
        test_all()
        show_times()
    else:
        mo = re.fullmatch(r'--all-dir=([\w-]+)', sys.argv[2])
        if mo:
            test_dirname = mo.group(1)
            test_all_in_dir(test_dirname)
        else:
            for test_file_arg in sys.argv[2:]:
                test_one(test_file_arg)
        show_times()

n_parse_calls = 0
total_parse_time = 0.0
n_ee_calls = 0
total_ee_time = 0.0

def show_times():
    print()
    if n_parse_calls:
        print(f"parse: {n_parse_calls} calls in {total_parse_time:.3} sec (avg {total_parse_time / n_parse_calls:.3} sec)")
    if n_ee_calls:
        print(f"early: {n_ee_calls} calls in {total_ee_time:.3} sec (avg {total_ee_time / n_ee_calls:.3} sec)")

def test_all():
    test_all_in_dir('fail')
    test_all_in_dir('early')
    test_all_in_dir('pass')
    test_all_in_dir('pass-explicit')
    # pseudocode_semantics.report_unused_entries()

def test_all_in_dir(test_dirname):
    print(test_dirname, file=sys.stderr)
    assert test_dirname in ['fail', 'early', 'pass', 'pass-explicit']
    output_filename = f'_test_parser/{test_dirname}_output.new'

    with open(output_filename, 'w', encoding='utf8') as f:
        dirpath = root_test_dirpath + "/" + test_dirname

        n_success = 0
        n_failure = 0
        for i, test_filename in enumerate(sorted(os.listdir(dirpath))):
            if re.fullmatch(r'\.\w+\.js.swp', test_filename):
                # vim temp file
                continue

            # if test_filename < 'f7f6': continue
            test_file_arg = test_dirname + '/' + test_filename

            if 0:
                sys.stderr.write(test_file_arg + '\n')
            else:
                if i % 20 == 0:
                    sys.stderr.write('.')
                    sys.stderr.flush()

            success = test_one(test_file_arg, f)
            if success:
                n_success += 1
            else:
                n_failure += 1

        sys.stderr.write('\n')
        print('====', file=f)
        print('Done', file=f)
        print(f"n_success = {n_success}", file=f)
        print(f"n_failure = {n_failure}", file=f)

def test_one(test_file_arg, f=sys.stdout):
    # Returns True if the test succeeded, False if it failed.

    print(file=f)
    print('===================', file=f)
    print(test_file_arg, file=f)
    print()
    print('XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX')
    print(test_file_arg)

    assert test_file_arg.endswith('.js')

    if test_file_arg.startswith('/'):
        # absolute path
        test_filepath = test_file_arg
        expectation = None
    else:
        # relative path, assumed to be relative to {root_test_dirpath}
        (test_dirname, test_filename) = test_file_arg.split('/')
        expectation = expectation_for_dirname(test_dirname)
        if test_file_arg in corrections:
            new_expectation = expectation_for_dirname(corrections[test_file_arg])
            print(f"(changing expectation from {expectation} to {new_expectation})", file=f)
            expectation = new_expectation

        test_filepath = root_test_dirpath + '/' + test_file_arg

    source_text = open(test_filepath,'r', encoding='utf-8', newline='').read()
    print(source_text, file=f)

    file_of_interest = 'xx005dc7dff71d4b97.js'
    # file_of_interest = '3dbb6e166b14a6c0.js'
    trace_level = (9 if test_filepath.endswith(file_of_interest) else 0)
    goal_symbol = 'Module' if test_filepath.endswith('.module.js') else 'Script'
    try:
        t_before = time.process_time()
        node = es_parser.parse(source_text, goal_symbol, trace_level=trace_level, trace_f=f)
        t_after = time.process_time()
    except es_parser.ParseError as pe:
        t_after = time.process_time()
        print(file=f)
        print('ParseError:', file=f)
        print(misc.display_position_in_text(source_text, pe.posn), end='', file=f)
        for item_string in pe.kernel_item_strings:
            print(f"    {item_string}", file=f)
        outcome = 'ParseError'
        if expectation is None:
            print(f"outcome: {outcome}")
        elif outcome == expectation:
            return True
        else:
            print(f"TEST {test_file_arg} FAILED: expected {expectation}, but got {outcome}", file=f)
            return False

    global n_parse_calls, total_parse_time
    n_parse_calls += 1
    total_parse_time += (t_after - t_before)

    if trace_level > 0: node.dump()

    if test_file_arg in [
        # 'pass/6b5e7e125097d439.js',
        # 'pass/714be6d28082eaa7.js',
        # 'pass/882910de7dd1aef9.js',
        # 'pass/dd3c63403db5c06e.js',
    ]:
        print('SKIPPING detect_early_errors due to seg fault', file=f)
        # investigate later
        return False

    pseudocode_semantics.reset_dynamic_state()
    t_before = time.process_time()
    early_errors = pseudocode_semantics.get_early_errors_in(node)
    t_after = time.process_time()
    if early_errors:
        print('Early Errors:', file=f)
        for ee in early_errors:
            print(file=f)
            print(ee.kind, file=f)
            print(misc.display_position_in_text(source_text, ee.location.start_posn), end='', file=f)
            print(ee.condition, file=f)
        outcome = 'early error'
    else:
        outcome = 'no error'

    global n_ee_calls, total_ee_time
    n_ee_calls += 1
    total_ee_time += (t_after - t_before)

    if expectation is None:
        print(f"outcome: {outcome}")
    elif outcome == expectation:
        return True
    else:
        print(f"TEST {test_file_arg} FAILED: expected {expectation}, but got {outcome}", file=f)
        node.dump(f=f)
        return False

def expectation_for_dirname(dirname):
    return {
        'fail'         : 'ParseError',
        'early'        : 'early error',
        'pass'         : 'no error',
        'pass-explicit': 'no error',
    }[dirname]

corrections = {

    # [will be fixed when PR #29 is merged:]
    # These 6 are in 'pass', but should be in 'fail'.
    # They contain an HTMLCloseComment, which (in a valid Script)
    # must be preceded by a LineTerminatorSequence or a /* ... LineTerminator ... */
    'pass/4f5419fe648c691b.js': 'fail',
    'pass/5a2a8e992fa4fe37.js': 'fail',
    'pass/5d5b9de6d9b95f3e.js': 'fail',
    'pass/946bee37652a31fa.js': 'fail',
    'pass/ba00173ff473e7da.js': 'fail',
    'pass/e03ae54743348d7d.js': 'fail',

    # [will be fixed when PR #31 is merged:]
    # In 'fail', should be in 'pass'.
    'fail/0d5e450f1da8a92a.js': 'pass',
    'fail/748656edbfb2d0bb.js': 'pass',
    'fail/79f882da06f88c9f.js': 'pass',
    'fail/92b6af54adef3624.js': 'pass',

    # [will be fixed when PR #32 is merged:]
    # These two are in 'early', but should be in 'fail'.
    # They raise a ParseError, but not due to an early error,
    # rather due to a "but only if" production-annotation.
    # Given the wording in test262-parser-tests/README.md,
    # they "do not match the grammar", so they should be in 'fail'.
    # See issue #15.
    'early/14eaa7e71c682461.js': 'fail',
    'early/aca911e336954a5b.js': 'fail',

    # [will be fixed when PR #33 is merged:]
    # In 'early', should be in 'fail':
    # PR #2392 replaced an Early Error with a more restrictive grammar.
    'early/1447683fba196181.js': 'fail',
    'early/d52f769ab39372c7.js': 'fail',

    # ------------

    # In 'fail', should be in 'pass':
    # PR #1668 Added |ClassElement : FieldDefinition `;`|
    # test262-parser-tests hasn't been updated re class fields
    # See https://freenode.logbot.info/tc39/20210515
    'fail/98204d734f8c72b3.js': 'pass',
    'fail/ef81b93cf9bdb4ec.js': 'pass',

    # In 'fail', should be in 'pass':
    # PR #614 "Normative: Allow initializers in ForInStatement heads"
    'fail/e3fbcf63d7e43ead.js': 'pass',

    # ---

    # These should be a parse error,
    # not due to the grammar, or an early error,
    # but rather a statement in prose.
    # So how should they be categorized?
    # 'fail/3c644395035bbe46.js': '?',
    # 'fail/534dac338ea83de6.js': '?',
    # 'fail/a5370cb0412d7c8a.js': '?',

    # ---

    # In 'fail', should be in 'early':
    'fail/abc46381e4e6bcca.js': 'early', # var \uD83B\uDE00 (early error is 11.6.1.1)

    # These are in 'fail', but should maybe be in 'early'.
    # Each involves a RegularExpressionLiteral,
    # which I believe is well-formed as such,
    # but which would not pass IsValidRegularExpressionLiteral,
    # which is invoked from an Early Error rule.
    'fail/66e383bfd18e66ab.js': 'early',
    'fail/78c215fabdf13bae.js': 'early',
    'fail/bf49ec8d96884562.js': 'early',
    'fail/e4a43066905a597b.js': 'early',

    # These are in 'fail', but should maybe be in 'early',
    # because when you have an instance of a Cover production,
    # reparsing of it (and raising of consequent Syntax Errors)
    # is instigated by Early Error rules.
    # (I don't know whether the expected failure of these
    # is supposed to be due to a reparse,
    # but I know that they're not currently raising a ParseError,
    # and they involve an instance of a Cover production.
    # But it could be a bug in my parser.)
    'fail/03d13b6c40f6aaea.js': 'early',
    'fail/08bafe059b17ac92.js': 'early',
    'fail/0bee7999482c66a0.js': 'early',
    'fail/0eb4ed330b5d7e2f.js': 'early',
    'fail/0ebf57bd8c051d27.js': 'early',
    'fail/0ff2a5bb12a4f5be.js': 'early',
    'fail/12f5bc355427b8f8.js': 'early',
    'fail/15de970e269ae56f.js': 'early',
    'fail/168502012959421f.js': 'early',
    'fail/16947dc1d11e5e70.js': 'early',
    'fail/175c1c09015415e1.js': 'early',
    'fail/19699bcdea35eb46.js': 'early',
    'fail/1a5b0dfa9fde985d.js': 'early',
    'fail/23368c25ea374e2f.js': 'early',
    'fail/2774b3cce5a09798.js': 'early',
    'fail/28520880d460c4f9.js': 'early',
    'fail/2884c585d2f035a5.js': 'early',
    'fail/295b0ed4d7872983.js': 'early',
    'fail/30f6acf0bf2f7f06.js': 'early',
    'fail/32529ec69f32cac1.js': 'early',
    'fail/346316bef54d805a.js': 'early',
    'fail/36c32455da0fd7e8.js': 'early',
    'fail/37e9fb0470e7ec3d.js': 'early',
    'fail/3990bb94b19b1071.module.js': 'early',
    'fail/3a3e59edfed719b0.js': 'early',
    'fail/3b6f737a4ac948a8.js': 'early',
    'fail/3d3e6ce2b81a224d.js': 'early',
    'fail/479332b63ff26de1.js': 'early',
    'fail/47b1abed697fe128.js': 'early',
    'fail/4c048218847a0242.js': 'early',
    'fail/4cce9feb5a563377.js': 'early',
    'fail/4e885526e8dfaa12.js': 'early',
    'fail/4ef1d6ca8eceb313.js': 'early',
    'fail/4fd864d1c4df25b0.js': 'early',
    'fail/50a060984b757dc1.js': 'early',
    'fail/54b72e05f42d7802.js': 'early',
    'fail/569a2c1bad3beeb2.js': 'early',
    'fail/5ab1050053c11514.js': 'early',
    'fail/5fae862d7fe6531c.js': 'early',
    'fail/618f5bdbe9497960.js': 'early',
    'fail/66e667cc2b718770.js': 'early',
    'fail/6ac4f95d48362a35.js': 'early',
    'fail/6dabf190eea04883.js': 'early',
    'fail/75b52e0f57aab958.js': 'early',
    'fail/783aeb8c90c3775d.js': 'early',
    'fail/794032efdfb20d41.js': 'early',
    'fail/7974c69bdfcceea8.js': 'early',
    'fail/7fe1dff1cf764f72.js': 'early',
    'fail/8053fd407fd3d848.js': 'early',
    'fail/80ea01a6fbf80920.js': 'early',
    'fail/81a5bf75eb66ff83.js': 'early',
    'fail/829d9261aa6cd22c.js': 'early',
    'fail/82b8003b91d8b346.js': 'early',
    'fail/88f3d521fae776b9.js': 'early',
    'fail/8bf8438d0a686b4e.js': 'early',
    'fail/8dc484a35dd0dc16.js': 'early',
    'fail/90cd97db35a1a503.js': 'early',
    'fail/91cb0ae4feb7f531.js': 'early',
    'fail/939b16a89d0e8704.js': 'early',
    'fail/95c10472e36270b6.js': 'early',
    'fail/976b6247ca78ab51.js': 'early',
    'fail/a028a9ab5777d337.js': 'early',
    'fail/a38011d2c010999e.js': 'early',
    'fail/a633b3217b5b8026.js': 'early',
    'fail/a793dd27762c8ec8.js': 'early',
    'fail/a8beb1480f385441.js': 'early',
    'fail/a9431906f263368d.js': 'early',
    'fail/ab9d14c2ef38f180.js': 'early',
    'fail/addee2ebe09cfa9c.js': 'early',
    'fail/b02cbe75ce1ceb06.js': 'early',
    'fail/b03ee881dce1a367.js': 'early',
    'fail/bcde05eea9466dfd.js': 'early',
    'fail/c045e273186c0644.js': 'early',
    'fail/c0ad1c20e662c8ed.js': 'early',
    'fail/c510fa0f191310ed.js': 'early',
    'fail/ca2716d236c027cd.js': 'early',
    'fail/ca27a03a9d04acd2.js': 'early',
    'fail/cb92787da5075fd1.js': 'early',
    'fail/cbc28b1205acaac8.js': 'early',
    'fail/cbc35276c97fcf51.js': 'early',
    'fail/cf23f5d7f2364a44.js': 'early',
    'fail/d012888b0c720723.js': 'early',
    'fail/d04aecd166354406.js': 'early',
    'fail/d55f938e1619ed72.js': 'early',
    'fail/db41a80ccf646002.js': 'early',
    'fail/dc14ac854168468f.js': 'early',
    'fail/dc5864c9096ad0a8.js': 'early',
    'fail/dfc6f1cc5533e0bb.js': 'early',
    'fail/e115bbef8bec1a84.js': 'early',
    'fail/e5fabf7fc4ae5dea.js': 'early',
    'fail/e7cf8728b0369efe.js': 'early',
    'fail/ebd282af4fda397d.js': 'early',
    'fail/ecec2a908f458adb.js': 'early',
    'fail/f08159ca58f10eb1.js': 'early',
    'fail/f0f498d6ae70038f.js': 'early',
    'fail/f30170f05890cff7.js': 'early',
    'fail/fc7ed197a376fa5f.js': 'early',

    # similarly, for LHSExpr:
    # (but even more chance that the expected parse error is for some other reason?)
    'fail/04bc213db9cd1130.js': 'early',
    'fail/06272e1e03d6ced7.js': 'early',
    'fail/0df19c6187ef3cbc.module.js': 'early',
    'fail/11d61dbd7c1fbd1b.js': 'early',
    'fail/1395e3a9d2acf65c.js': 'early',
    'fail/147fa078a7436e0e.js': 'early',
    'fail/14d6adc74d396c58.js': 'early',
    'fail/15a6123f6b825c38.js': 'early',
    'fail/1a32df2e8d4bea98.js': 'early',
    'fail/1ad1143aa95cf8bf.js': 'early',
    'fail/1b87f4048bac9335.js': 'early',
    'fail/1c04d8bc2ab25c1e.js': 'early',
    'fail/2226edabbd2261a7.module.js': 'early',
    'fail/2b8d54f6fc1dcbd6.js': 'early',
    'fail/2d46c7c14cfb0330.js': 'early',
    'fail/2e95646f9143563e.js': 'early',
    'fail/3078b4fed5626e2a.js': 'early',
    'fail/328fddc7bdffb499.js': 'early',
    'fail/38816d56f582672f.js': 'early',
    'fail/3bc2b27a7430f818.js': 'early',
    'fail/4485930b35bf8cb6.js': 'early',
    'fail/4882f5db31935a04.js': 'early',
    'fail/4a887c2761eb95fb.js': 'early',
    'fail/4ce3c0a393c624d5.js': 'early',
    'fail/4f0b15bd78646107.js': 'early',
    'fail/5301846f80919b63.js': 'early',
    'fail/531ee852cc8ed0a7.js': 'early',
    'fail/5c63ac420337d014.js': 'early',
    'fail/5d42f9f543d5f55c.js': 'early',
    'fail/5e6f67a0e748cc42.js': 'early',
    'fail/66abd1d09c28ada8.js': 'early',
    'fail/68766c3f46c4851a.js': 'early',
    'fail/721efc4cbc95a6a0.js': 'early',
    'fail/75f1656578c2d7e8.js': 'early',
    'fail/7624feb2a003e001.js': 'early',
    'fail/78e861dca5c2377d.js': 'early',
    'fail/80bfa9f27278bbba.js': 'early',
    'fail/851bfeb09635c752.js': 'early',
    'fail/87dfd34c1ed7ab04.js': 'early',
    'fail/8cf27fd80ffbc24e.js': 'early',
    'fail/8fdb7e6ddfb89e3a.js': 'early',
    'fail/938db8c9f82c8cb5.module.js': 'early',
    'fail/95682e688db64065.js': 'early',
    'fail/974222e3683f284a.js': 'early',
    'fail/9f15affa01060595.js': 'early',
    'fail/9f5a6dae7645976a.js': 'early',
    'fail/9fa56398be8a1769.js': 'early',
    'fail/a0998570a3bf9869.js': 'early',
    'fail/aa232c1eb3da8805.js': 'early',
    'fail/ab35979364766bf0.js': 'early',
    'fail/ae0a7ac275bc9f5c.js': 'early',
    'fail/af3a9b653481f43a.js': 'early',
    'fail/b3b14fb0e398703d.js': 'early',
    'fail/b7b057684207633b.js': 'early',
    'fail/b9422ea5edcddf0b.js': 'early',
    'fail/befeaa367d8f27db.js': 'early',
    'fail/bfadeead1ddbd122.js': 'early',
    'fail/c0a8cdfa09f3b86c.js': 'early',
    'fail/c5af6ad6ff9d213f.js': 'early',
    'fail/ce7800f269603948.js': 'early',
    'fail/d0804b4856dbb6be.module.js': 'early',
    'fail/d201e6e384a593bb.js': 'early',
    'fail/d28e80d99f819136.js': 'early',
    'fail/d4cf8ae9018f6a28.js': 'early',
    'fail/d5bc0fb6d6e472cb.js': 'early',
    'fail/ea4d962dac83e2a1.js': 'early',
    'fail/f0f16b655e08b92c.js': 'early',
    'fail/f4c0cdc8d5782f3f.js': 'early',
    'fail/f51aea0352bb03f3.js': 'early',
    'fail/f6924dd818b18733.js': 'early',
    'fail/f6cc48c72caf2e32.js': 'early',

}

# duplicate file names:
# 14eaa7e71c682461.js
# 2e95646f9143563e.js
# a633b3217b5b8026.js
# aca911e336954a5b.js

main()

# vim: sw=4 ts=4 expandtab
