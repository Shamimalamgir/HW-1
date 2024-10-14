import ply.yacc as yacc
import ply.lex as lex

tokens = (
    'VAR',
    'CONJUNCTION', 'DISJUNCTION', 'IMPLICATION', 'NEGATION',
    'LPAREN', 'RPAREN',
)

t_VAR = r'[a-z]'
t_CONJUNCTION = r'/\\'
t_DISJUNCTION = r'\\/'
t_IMPLICATION = r'->'
t_NEGATION = r'~'
t_LPAREN = r'\('
t_RPAREN = r'\)'

t_ignore = ' \t'

lexer = lex.lex()


class Unit:
    def __init__(self, value):
        self.value = value
        self.negation = False

    def printable(self):
        return "~" + self.value if self.negation else self.value


class Clause_sat:
    def __init__(self, unit1, unit2):
        self.units = [unit1, unit2]
        self.tautology = False
        self.satisfiable = True
        if unit1.value == unit2.value:
            if unit1.negation != unit2.negation:
                self.tautology = True
            elif unit1.value is None:
                self.satisfiable = False
            else:
                self.units[0] = Unit(None)


class Expression:
    def __init__(self, clauses):
        self.clauses = clauses
        self.satisfied = None

    def result(self):
        return self.satisfied

    def reduce_tautology(self):
        n = len(self.clauses)
        for i in range(n):
            clause = self.clauses[n - i - 1]
            if clause.tautology: self.clauses.remove(clause)

    def check_duplicate(self, new_clause):
        for clause in self.clauses:
            if all(
                    any(
                        (new_unit.value == existing_unit.value and
                         new_unit.negation == existing_unit.negation)
                        for existing_unit in clause.units
                    )
                    for new_unit in new_clause.units
            ):
                return True
        return False

    def apply_resolution(self):
        self.satisfied = True
        while True:
            len_clauses = len(self.clauses)
            clauses = list(self.clauses)
            new_clauses = []

            for clause_i in clauses:
                for clause_j in clauses:
                    if clause_i == clause_j:
                        continue

                    for i in range(2):
                        for j in range(2):
                            unit_i = clause_i.units[i]
                            unit_j = clause_j.units[j]

                            if unit_i.value == unit_j.value and unit_i.negation != unit_j.negation:
                                new_clause = Clause_sat(clause_i.units[i ^ 1], clause_j.units[j ^ 1])

                                if not new_clause.satisfiable:
                                    self.clauses.append(new_clause)
                                    self.satisfied = False
                                    return

                                if not new_clause.tautology and not self.check_duplicate(new_clause):
                                    new_clauses.append(new_clause)

            self.clauses.extend(new_clauses)

            if len_clauses == len(self.clauses):
                return


def p_expression_conjunction(p):
    'expression : expression CONJUNCTION expression'
    p[0] = Expression(p[1].clauses + p[3].clauses)


def p_expression_paren(p):
    'expression : LPAREN expression RPAREN'
    p[0] = p[2]


def p_expression_clause(p):
    'expression : clause'
    p[0] = Expression([p[1]])


def p_clause_implication(p):
    'clause : unit IMPLICATION unit'
    p[1].negation = not p[1].negation
    p[0] = Clause_sat(p[1], p[3])


def p_clause_disjunction(p):
    'clause : unit DISJUNCTION unit'
    p[0] = Clause_sat(p[1], p[3])


def p_clause_unit(p):
    'clause : unit'
    p[0] = Clause_sat(p[1], Unit(None))


def p_unit_negation(p):
    'unit : NEGATION unit'
    p[0] = p[2]
    p[0].negation = True


def p_unit_var(p):
    'unit : VAR'
    p[0] = Unit(p[1])


parser = yacc.yacc()


def is_satisfiable(input_str):
    result = parser.parse(input_str)
    if result is not None:
        result.reduce_tautology()
        result.apply_resolution()
        return result.result()
