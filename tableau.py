MAX_CONSTANTS = 10
MAX_EXPAND = 1000
QUANTIFIERS = ["A", "E"]
PROPOSITIONS = ["p", "q", "r", "s"]
PREDICATES = ["P", "Q", "R", "S"]
CONNECTIVES = ["^", "v", ">"]
VAR = ["x", "y", "z", "w"]
DEBUG_PARSER = False
DEBUG_SAT = False

constants = []


# Parse a formula, consult parseOutputs for return values.
def parse(fmla):
    result = 0

    if len(fmla) != 0:
        if fmla[0] == "-":
            # 7 / 2 / 0 - Negatived
            first_non_neg = 1
            # clean double negations
            while first_non_neg < len(fmla) and fmla[first_non_neg] == "-":
                first_non_neg += 1
            next_parsed = parse(fmla[first_non_neg:])
            if next_parsed in [6, 8]:
                result = 7  # Neg Proposition
            elif next_parsed in [3, 4, 5, 1]:
                result = 2  # Neg first order
        elif fmla[0] in QUANTIFIERS:
            # 3 / 4 / 0 - Quantified
            if fmla[1] in VAR:
                next_parsed = parse(fmla[2:])
                if next_parsed > 0:
                    # Ax / Ex
                    result = 3 if fmla[0] == QUANTIFIERS[0] else 4

        elif fmla[0] == "(":
            # 5 / 8 / 0 - binary connectives
            if fmla[-1] == ")":
                l_parsed = parse(lhs(fmla))
                r_parsed = parse(rhs(fmla))
                if DEBUG_PARSER:
                    print('>>', lhs(fmla), con(fmla), rhs(fmla))
                if con(fmla) in CONNECTIVES and l_parsed > 0 and r_parsed > 0:
                    if l_parsed < 6 or r_parsed < 6:
                        result = 5  # binary first order
                    else:
                        result = 8  # binary proposition

        elif fmla[0] in PROPOSITIONS and len(fmla) == 1:
            # 6 / 0 - Propositions
            result = 6
        elif fmla[0] in PREDICATES:
            # 1 / 0 - Predicates
            result = 1
            if fmla[1] == "(" and fmla[-1] == ")":
                inner_fmlas = fmla[2:-1].split(',')
                for inner_fmla in inner_fmlas:
                    if inner_fmla not in VAR and parse(inner_fmla) == 0:
                        result = 0
                        break
    if DEBUG_PARSER:
        print(fmla, result)
    return result


def get_con_idx(fmla):
    l_count = 0
    con_idx = -1
    for idx, elem in enumerate(fmla[1:]):
        if elem == "(":
            l_count += 1
        elif elem == ")":
            l_count -= 1
        if l_count == 0:
            if elem in CONNECTIVES:
                con_idx = idx + 1
                break
        elif l_count < 0:
            break
    return con_idx


# Return the LHS of a binary connective formula
def lhs(fmla):
    return fmla[1:get_con_idx(fmla)]


# Return the connective symbol of a binary connective formula
def con(fmla):
    return fmla[get_con_idx(fmla)]


# Return the RHS symbol of a binary connective formula
def rhs(fmla):
    return fmla[get_con_idx(fmla) + 1:-1]


# You may choose to represent a theory as a set or a list
# fmla should be a correct formula
# a theory is a list of fmlas
def theory(fmla):  # initialise a theory with a single formula in it
    if DEBUG_PARSER:
        print(">> Theory:", fmla)
    return [fmla]


# check for satisfiability
# Tableau tab is [theory(fmla)]
def sat(tab):
    TYPES = ['a', 'b', 'd', 'y']

    def _exp(this_theory):
        for fml in this_theory:
            if parse(fml) in [2, 7]:
                if parse(fml[1:]) not in [1, 6]:
                    return False
            elif parse(fml) not in [1, 6]:
                return False
        return True

    def _c(this_theory):
        exist = []
        for fml in this_theory:
            if fml[0] == '-':
                if fml[1:] in exist:
                    return True
            else:
                if ("-" + fml) in exist:
                    return True
            exist.append(fml)
        return False

    def _sai(this_theory):
        rlt = {
            "type": None,
            "arg": None
        }
        fmla_parsed = parse(this_theory)
        if fmla_parsed in [2, 7]:
            next_theory = this_theory[1:]
            next_parsed = parse(next_theory)
            if next_parsed in [2, 7]:  # alpha 2
                rlt['type'] = TYPES[0]
                rlt['arg'] = [this_theory[2:]]
            elif next_parsed in [5, 8]:
                connective = con(next_theory)
                if connective == CONNECTIVES[0]:  # beta 3 -AND
                    rlt['type'] = TYPES[1]
                    rlt['arg'] = ['-' + lhs(this_theory), '-' + rhs(this_theory)]
                elif connective == CONNECTIVES[1]:  # alpha 3 -OR
                    rlt['type'] = TYPES[0]
                    rlt['arg'] = ['-' + lhs(this_theory), '-' + rhs(this_theory)]
                elif connective == CONNECTIVES[2]:  # alpha 4 -OR>
                    rlt['type'] = TYPES[0]
                    rlt['arg'] = [lhs(this_theory), '-' + rhs(this_theory)]
                else:
                    print('err 2,7')
            elif next_parsed == 3:  # quantifier A
                rlt['type'] = TYPES[4]
                new_fmla = '-' + this_theory[2:]
                rlt['arg'] = [new_fmla]
            elif next_parsed == 4:  # quantifier E
                rlt['type'] = TYPES[3]
            elif DEBUG_SAT:
                print('err')
        elif fmla_parsed in [5, 8]:
            connective = con(this_theory)
            if connective == CONNECTIVES[0]:  # alpha 1 AND
                rlt['type'] = TYPES[0]
                rlt['arg'] = [lhs(this_theory), rhs(this_theory)]
            elif connective == CONNECTIVES[1]:  # beta 1 OR
                rlt['type'] = TYPES[1]
                rlt['arg'] = [lhs(this_theory), rhs(this_theory)]
            elif connective == CONNECTIVES[2]:  # beta 4 OR>
                rlt['type'] = TYPES[1]
                rlt['arg'] = ['-' + lhs(this_theory), rhs(this_theory)]
            elif DEBUG_SAT:
                print('err 5,8')
        elif fmla_parsed in [3, 4]:
            print('skipped gama delta')
            pass  # quantifier
        elif fmla_parsed in [1, 6]:
            pass
        elif DEBUG_SAT:
            print('not a formula')
        return rlt

    result = 0
    expand_count = 0
    while len(tab) != 0 and expand_count < MAX_EXPAND:
        # sigma this a theory
        sigma = tab.pop(0)
        if _exp(sigma) and not _c(sigma):
            result = 1
            break
        else:
            for fmla in sigma:
                sai = _sai(fmla)
                args = sai['arg']
                if sai['type'] == TYPES[0]:  # alpha
                    if not _c(args) and args not in tab:
                        tab.append(args)
                elif sai['type'] == TYPES[1]:  # beta
                    for formula in args:
                        arg = [formula]
                        if not _c(arg) and arg not in tab:
                            tab.append(arg)
                elif sai['type'] == TYPES[2]:  # delta
                    pass
                elif sai['type'] == TYPES[3]:  # gama
                    pass
        expand_count += 0
    if DEBUG_SAT and expand_count == MAX_EXPAND:
        print("reached maximum expansion")

    # output 0 if not satisfiable,
    # output 1 if satisfiable,
    # output 2 if number of constants exceeds MAX_CONSTANTS
    return result


# ########################################
# comment the following before submitting
# ########################################
f = open('input_no_fol.txt')

parseOutputs = ['not a formula',
                'an atom',
                'a negation of a first order logic formula',
                'a universally quantified formula',
                'an existentially quantified formula',
                'a binary connective first order formula',
                'a proposition',
                'a negation of a propositional formula',
                'a binary connective propositional formula']

satOutput = ['is not satisfiable', 'is satisfiable', 'may or may not be satisfiable']

firstline = f.readline()

PARSE = False
if 'PARSE' in firstline:
    PARSE = True

SAT = False
if 'SAT' in firstline:
    SAT = True

for line in f:
    if DEBUG_PARSER:
        print("vvvvvvvvvvvvvvvvvvvvvvvvvv")
    if line[-1] == '\n':
        line = line[:-1]
    parsed = parse(line)

    if PARSE:
        output = "%s is %s." % (line, parseOutputs[parsed])
        if parsed in [5, 8]:
            output += " Its left hand side is %s, its connective is %s, and its right hand side is %s." % (
                lhs(line), con(line), rhs(line))
        print(output)
    if DEBUG_PARSER:
        print("--------------------------")
    if SAT:
        if parsed:
            tableau = [theory(line)]
            print('%s %s.' % (line, satOutput[sat(tableau)]))
        else:
            print('%s is not a formula.' % line)

    if DEBUG_PARSER:
        print("^^^^^^^^^^^^^^^^^^^^^^^^^^")

# Original skeleton
# DO NOT MODIFY THE CODE BELOW
# f = open('input.txt')
#
# parseOutputs = ['not a formula',
#                 'an atom',
#                 'a negation of a first order logic formula',
#                 'a universally quantified formula',
#                 'an existentially quantified formula',
#                 'a binary connective first order formula',
#                 'a proposition',
#                 'a negation of a propositional formula',
#                 'a binary connective propositional formula']
#
# satOutput = ['is not satisfiable', 'is satisfiable', 'may or may not be satisfiable']
#
# firstline = f.readline()
#
# PARSE = False
# if 'PARSE' in firstline:
#     PARSE = True
#
# SAT = False
# if 'SAT' in firstline:
#     SAT = True
#
# for line in f:
#     if line[-1] == '\n':
#         line = line[:-1]
#     parsed = parse(line)
#
#     if PARSE:
#         output = "%s is %s." % (line, parseOutputs[parsed])
#         if parsed in [5, 8]:
#             output += " Its left hand side is %s, its connective is %s, and its right hand side is %s." % (
#                 lhs(line), con(line), rhs(line))
#         print(output)
#
#     if SAT:
#         if parsed:
#             tableau = [theory(line)]
#             print('%s %s.' % (line, satOutput[sat(tableau)]))
#         else:
#             print('%s is not a formula.' % line)
