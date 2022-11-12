QUANTIFIERS = ["A", "E"]
PROPOSITIONS = ["p", "q", "r", "s"]
PREDICATES = ["P", "Q", "R", "S"]
CONNECTIVES = ["^", "v", ">"]
DEBUG_SAT = True


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


result = _no_free_var('Ax(P(a,a)^Ex-P(a,x))', 'x')
print(result)