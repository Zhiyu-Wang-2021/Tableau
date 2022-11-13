MAX_CONSTANTS = 10
MAX_EXPAND = 1000
QUANTIFIERS = ["A", "E"]
PROPOSITIONS = ["p", "q", "r", "s"]
PREDICATES = ["P", "Q", "R", "S"]
CONNECTIVES = ["^", "v", ">"]
VAR = ["x", "y", "z", "w"]
DEBUG_PARSER = False
DEBUG_SAT = False
CONSTANTS = [chr(97 + i) for i in range(MAX_CONSTANTS)]


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
                if len(inner_fmlas) == 2:
                    for inner_fmla in inner_fmlas:
                        if (inner_fmla not in VAR and inner_fmla not in CONSTANTS) and parse(inner_fmla) == 0:
                            result = 0
                            break
                else:
                    result = 0
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
    TYPES = ['a', 'b', 'd', 'y', 'p']
    constants = []

    used_constants_by = {}

    # determine whether a theory is fully expanded
    def _exp(this_theory):
        for fml in this_theory:
            if parse(fml) in [2, 7]:
                if parse(fml[1:]) not in [1, 6]:
                    return False
            elif parse(fml) not in [1, 6]:
                return False
        return True

    # determine whether a theory contradicts itself
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

    # determine which type of action to take
    # and the arguments needed
    def _sai(this_theory):
        rlt = {
            "type": None,
            "arg": None
        }
        if DEBUG_SAT:
            print("theory:", this_theory)
        # this_theory = _reorder_quantifiers(this_theory)
        fmla_parsed = parse(this_theory)
        if DEBUG_SAT:
            print("theory reordered:", this_theory, "parse result:", fmla_parsed)
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
                    rlt['arg'] = ['-' + lhs(next_theory), '-' + rhs(next_theory)]
                elif connective == CONNECTIVES[1]:  # alpha 3 -OR
                    rlt['type'] = TYPES[0]
                    rlt['arg'] = ['-' + lhs(next_theory), '-' + rhs(next_theory)]
                elif connective == CONNECTIVES[2]:  # alpha 4 -OR>
                    rlt['type'] = TYPES[0]
                    rlt['arg'] = [lhs(next_theory), '-' + rhs(next_theory)]
                else:
                    if DEBUG_SAT:
                        print('err 2,7')
            elif next_parsed == 4:  # quantifier -E, y
                rlt['type'] = TYPES[3]
                rlt['arg'] = ['-' + next_theory[2:], next_theory[1], this_theory]
            elif next_parsed == 3:  # quantifier -A, d
                if len(constants) == MAX_CONSTANTS:
                    if DEBUG_SAT:
                        print('err max')
                else:
                    rlt['type'] = TYPES[2]
                    constants.append(chr(97 + len(constants)))
                    if DEBUG_SAT:
                        print('constants:', constants, 'len:', len(constants))
                    rlt['arg'] = ['-' + next_theory[2:], next_theory[1], constants[-1]]
            elif next_parsed in [1, 6]:
                if DEBUG_SAT:
                    print('sai 1, 6')
                rlt['type'] = TYPES[4]
                rlt['arg'] = [this_theory]
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
        elif fmla_parsed == 3:  # quantifier A, y
            rlt['type'] = TYPES[3]
            rlt['arg'] = [this_theory[2:], this_theory[1], this_theory]
        elif fmla_parsed == 4:  # quantifier E, d
            if len(constants) == MAX_CONSTANTS:
                if DEBUG_SAT:
                    print('err max')
            else:
                rlt['type'] = TYPES[2]
                constants.append(chr(97 + len(constants)))
                if DEBUG_SAT:
                    print('constants:', constants, 'len:', len(constants))
                rlt['arg'] = [this_theory[2:], this_theory[1], constants[-1]]
        elif fmla_parsed in [1, 6]:
            if DEBUG_SAT:
                print('sai 1, 6')
            rlt['type'] = TYPES[4]
            rlt['arg'] = [this_theory]
        elif DEBUG_SAT:
            print('not a formula or other err')
        return rlt

    def _replace_in_scope(this_fmla, target, sub):
        if DEBUG_SAT:
            print(this_fmla, target, sub)
        is_inner = False
        is_quantifier = False
        num_left = 0
        rlt = this_fmla[:2]
        for i in range(len(this_fmla) - 2):

            this_char = this_fmla[i + 2]

            if not is_quantifier:
                if not is_inner:
                    if this_char in QUANTIFIERS:
                        is_inner = True
                        is_quantifier = True
                    elif this_char == target:
                        this_char = sub
                else:
                    if this_char == '(':
                        num_left += 1
                    elif this_char == ')':
                        num_left -= 1
                    elif num_left == 0 and this_char in CONNECTIVES:
                        is_inner = False
            else:
                if this_char != target:
                    is_inner = False
                is_quantifier = False

            rlt += this_char
        return rlt

    def _no_free_var(this_fmla, target):
        if DEBUG_SAT:
            print(this_fmla, target)
        is_inner = False
        is_quantifier = False
        num_left = 0
        rlt = True
        for i in range(len(this_fmla) - 2):

            this_char = this_fmla[i + 2]

            if not is_quantifier:
                if not is_inner:
                    if this_char in QUANTIFIERS:
                        is_inner = True
                        is_quantifier = True
                    elif this_char == target:
                        rlt = False
                        break
                else:
                    if this_char == '(':
                        num_left += 1
                    elif this_char == ')':
                        num_left -= 1
                    elif num_left == 0 and this_char in CONNECTIVES:
                        is_inner = False
            else:
                if this_char != target:
                    is_inner = False
                is_quantifier = False

        return rlt

    def _clean_double_neg(this_fmla):
        rlt = []
        for c in this_fmla:
            if c == '-' and len(rlt) > 0 and rlt[-1] == '-':
                rlt.pop()
            else:
                rlt.append(c)
        return ''.join(rlt)

    def _reorder_quantifiers(this_fmla):
        this_fmla = _clean_double_neg(this_fmla)
        if parse(this_fmla) < 6:
            reordered_quantifiers = ""
            this_parsed = parse(this_fmla)
            while this_parsed in [3, 4, 2]:
                is_neg = this_parsed == 2
                if is_neg:
                    this_fmla = this_fmla[1:]
                    this_parsed = parse(this_fmla)
                if this_parsed in [3, 4]:
                    if this_parsed == 3:  # Ax
                        if is_neg:  # -Ax
                            reordered_quantifiers = '-' + this_fmla[:2] + reordered_quantifiers
                        else:  # Ax
                            reordered_quantifiers += this_fmla[:2]
                    elif this_parsed == 4:
                        if is_neg:  # -Ex
                            reordered_quantifiers += '-' + this_fmla[:2]
                        else:  # Ex
                            reordered_quantifiers = this_fmla[:2] + reordered_quantifiers
                    this_fmla = this_fmla[2:]
                    this_parsed = parse(this_fmla)
                elif this_parsed in [1, 5] and is_neg:
                    reordered_quantifiers += "-"
            reordered_quantifiers += this_fmla
            return reordered_quantifiers
        else:
            return this_fmla

    def _reorder_sigma(this_sigma):
        reordered_sigma = this_sigma.copy()
        if parse(this_sigma[0]) == 3:
            for index, this_fmla in enumerate(this_sigma):
                if parse(this_fmla) == 4:
                    reordered_sigma[0], reordered_sigma[index] = reordered_sigma[index], reordered_sigma[0]
        return reordered_sigma

    # ########################################
    #       determine the satisfiability
    # ########################################

    result = 0
    expand_count = 0
    while len(tab) != 0 and expand_count < MAX_EXPAND:
        expand_count += 1
        if DEBUG_SAT:
            print("tab: ", tab)
            print("////////////  TAB  ////////////\n")
        # sigma this a theory
        sigma = tab.pop(0)
        sigma = _reorder_sigma(sigma)
        if _exp(sigma) and not _c(sigma):
            if DEBUG_SAT:
                print(">> fully expanded and no contradiction", sigma)
            result = 1
            break
        else:
            if DEBUG_SAT:
                print(">> sigma", sigma)
            # only process the first element of sigma
            # eventually everyone would be processed as it rotates while appending
            fmla = sigma[0]
            rest_of_sigma = sigma[1:]
            sai = _sai(fmla)
            args = sai['arg']
            if DEBUG_SAT:
                print(">> sai", sai)
            if sai['type'] == TYPES[0]:  # alpha
                sig = rest_of_sigma.copy()
                for formula in args:
                    if formula not in sig:
                        sig += [formula]
                if not _c(sig) and sig not in tab:
                    tab.append(sig)
            elif sai['type'] == TYPES[1]:  # beta
                for formula in args:
                    sig = rest_of_sigma.copy()
                    if formula not in sig:
                        sig += [formula]
                    if not _c(sig) and sig not in tab:
                        tab.append(sig)
            elif sai['type'] == TYPES[2]:  # delta
                # need to consider the scope of free variables

                arg = [_replace_in_scope(args[0], args[1], args[2])]
                if DEBUG_SAT:
                    print("after replace:", arg)
                # arg = [args[0].replace(args[1], args[2])]  # theory x -> a
                sig = rest_of_sigma.copy()
                if arg not in sig:
                    sig += arg
                if not _c(sig) and sig not in tab:
                    tab.append(sig)
            elif sai['type'] == TYPES[3]:  # gama
                if DEBUG_SAT:
                    print("!!!!!!!!! Gama !!!!!!!!!!!")
                # for each char in all formulas in sigma
                original_fmla = args[2]
                this_target = args[1]
                if _no_free_var(original_fmla, this_target):
                    tab.append([original_fmla[2:]])
                else:
                    found = False
                    for fml in sigma:
                        for c in fml:
                            if c in constants:
                                # arg = [args[0].replace(args[1], c)]
                                arg = [_replace_in_scope(args[0], this_target, c)]

                                if arg not in sigma:
                                    sig = rest_of_sigma.copy() + arg + [original_fmla]
                                    if not _c(sig) and sig not in tab:
                                        if original_fmla not in used_constants_by.keys():
                                            used_constants_by[original_fmla] = [c]
                                            tab.append(sig)
                                            found = True
                                            break
                                        elif c not in used_constants_by[original_fmla]:
                                            used_constants_by[original_fmla].append(c)
                                            tab.append(sig)
                                            found = True
                                            break
                                    elif _c(sig):
                                        if DEBUG_SAT:
                                            print("find gamma contradiction")
                                            print('sig:', sig)
                                        found = True
                                        result = 0
                                        break

                        if found:
                            break
                    if not found:
                        if DEBUG_SAT:
                            print("discard Ax as all case tried")
                        tab.append(rest_of_sigma.copy())
                    else:
                        if DEBUG_SAT:
                            print("----------USED CONSTANT------------")
                            print(used_constants_by)
                            print("----------USED CONSTANT------------")
            elif sai['type'] == TYPES[4]:  # 1, 6
                tab.append(rest_of_sigma + [args[0]])
    if expand_count >= MAX_EXPAND:
        result = 2
        if DEBUG_SAT:
            print("reached maximum expansion")

    elif len(tab) == 0:
        if DEBUG_SAT:
            print('nothing left in tableau')

    # output 0 if not satisfiable,
    # output 1 if satisfiable,
    # output 2 if number of constants exceeds MAX_CONSTANTS
    return result

# DO NOT MODIFY THE CODE BELOW
f = open('input.txt')

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
    if line[-1] == '\n':
        line = line[:-1]
    parsed = parse(line)

    if PARSE:
        output = "%s is %s." % (line, parseOutputs[parsed])
        if parsed in [5, 8]:
            output += " Its left hand side is %s, its connective is %s, and its right hand side is %s." % (
                lhs(line), con(line), rhs(line))
        print(output)

    if SAT:
        if parsed:
            tableau = [theory(line)]
            print('%s %s.' % (line, satOutput[sat(tableau)]))
        else:
            print('%s is not a formula.' % line)

