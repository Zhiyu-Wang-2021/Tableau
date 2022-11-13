MAX_CONSTANTS = 10
MAX_EXPAND = 30
QUANTIFIERS = ["A", "E"]
PROPOSITIONS = ["p", "q", "r", "s"]
PREDICATES = ["P", "Q", "R", "S"]
CONNECTIVES = ["^", "v", ">"]
VAR = ["x", "y", "z", "w"]
DEBUG_PARSER = False
DEBUG_SAT = True
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
                for inner_fmla in inner_fmlas:
                    if (inner_fmla not in VAR and inner_fmla not in CONSTANTS) and parse(inner_fmla) == 0:
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


# result = _no_free_var('Ax(P(a,a)^Ex-P(a,x))', 'x')
result = _reorder_quantifiers('Ax-Ey-Az-EzAyExP(x,y)')
print(result, result == 'Ex-AzAx-Ey-EzAyP(x,y)')
result = _reorder_quantifiers('-P(x,y)')
print(result, result == '-P(x,y)')
result = _reorder_quantifiers('-(P(x,y)^Ax-Ey-Az-EzAyExP(x,y))')
print(result, result == '-(P(x,y)^Ax-Ey-Az-EzAyExP(x,y))')
result = _reorder_quantifiers('Ax-Ey-Az-EzAyEx(P(x,y)>P(y,x))')
print(result, result == 'Ex-AzAx-Ey-EzAy(P(x,y)>P(y,x))')
result = _reorder_quantifiers('-Ax-Ey-Az-EzAyEx(P(x,y)>P(y,x))')
print(result, result == 'Ex-Az-Ax-Ey-EzAy(P(x,y)>P(y,x))')
result = _reorder_quantifiers('-Ax-Ey-Az-EzAyExP(x,y)')
print(result, result == 'Ex-Az-Ax-Ey-EzAyP(x,y)')
result = _reorder_quantifiers('-Ax-Ey-P(x,y)')
print(result, result == '-Ax-Ey-P(x,y)')
result = _reorder_quantifiers('-----------q')
print(result, result == '-Ax-Ey-P(x,y)')
result = _reorder_quantifiers('----Ax----Ey----P(x,y)')
print(result, result == 'EyAxP(x,y)')
