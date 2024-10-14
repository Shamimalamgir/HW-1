import ply.yacc as yacc
import ply.lex as lex
from lex_file import Clause


class CNF:
    def __init__(self, *clauses):
        self._clauses_set = set(clauses)
        self._clauses = list(self._clauses_set)

    @property
    def clauses(self):
        return self._clauses

    def add_clause(self, clause):
        # Check if the clause is valid before adding
        if (
                clause.literals is not None and
                clause not in self._clauses_set and
                clause != Clause()
        ):
            self._clauses.append(clause)
            self._clauses_set.add(clause)

    def add_assignment(self, assignment):
        new_clauses = set()

        for clause in self._clauses_set:
            new_literals = set()

            for literal in clause.literals:
                if literal.variable not in assignment:
                    new_literals.add(literal)
                elif assignment[literal.variable] != literal.add_negation:
                    new_literals.clear()  # Clear the set and break
                    break

            if new_literals:
                new_clauses.add(Clause(*new_literals))

        self._clauses_set = new_clauses
        self._clauses = list(self._clauses_set)  # Update the list of clauses


def saturate(cnf: CNF) -> CNF:
    cur_clause_index = 1

    while cur_clause_index < len(cnf.clauses):
        current_clause = cnf.clauses[cur_clause_index]
        current_literals = current_clause.literals

        for clause in cnf.clauses[:cur_clause_index]:
            for literal in clause.literals:
                if literal.negative() in current_literals:
                    new_clause = current_clause & clause

                    if new_clause is None:
                        return CNF()  # Return an empty CNF if new_clause is None

                    cnf.add_clause(new_clause)  # Add the combined clause to CNF

        cur_clause_index += 1

    return cnf  # Return the modified CNF


# ----------------------------------------------------------------
tokens = (
    'VAR',
    'LBRACKET',
    'RBRACKET',
    'NEGATION',
    'CONJUNCTION',
    'DISJUNCTION',
    'IMPLICATION'
)

t_VAR = r'[a-z]'
t_LBRACKET = r'\('
t_RBRACKET = r'\)'
t_NEGATION = r'\~'
t_CONJUNCTION = r'/\\'
t_DISJUNCTION = r'\\/'
t_IMPLICATION = r'->'

t_ignore = ' '


class ParserCNF:
    def __init__(self, *clauses):
        self.clauses = list(clauses)

    def linearized_clauses(self):
        linearized = []

        for clause in self.clauses:
            if isinstance(clause, ParserCNF):
                linearized.extend(clause.linearized_clauses())  # Use extend for better performance
            else:
                linearized.append(clause)

        return linearized


def p_cnf(p):
    '''cnf : clause CONJUNCTION cnf
           | clause
    '''
    if len(p) == 2:
        p[0] = ParserCNF(p[1])
    else:
        p[0] = ParserCNF(p[1], p[3])


def p_clause(p):
    '''clause : LBRACKET literal DISJUNCTION literal RBRACKET
              | LBRACKET literal IMPLICATION literal RBRACKET
              | literal
              | LBRACKET literal RBRACKET'''
    if len(p) == 4:
        p[0] = Clause(p[2])
    elif len(p) == 2:
        p[0] = Clause(p[1])
    elif p[3] == '->':
        p[0] = Clause(p[2].negative(), p[4])
    else:
        p[0] = Clause(p[2], p[4])


def p_literal(p):
    '''literal : NEGATION VAR
               | VAR'''
    if p[1] == '~':
        p[0] = Literal(p[2], True)
    else:
        p[0] = Literal(p[1], False)


def parse_line(self, s: str):
    # Parse the input string into a CNF structure
    result: ParserCNF = self.parser.parse(s)

    # Return the linearized clauses from the parsed result
    return result.linearized_clauses()


from lex_file import Parser


def sat_assignment(formula):
    clauses = Parser().parse(formula)
    cnf = CNF(*clauses)

    unused_variables = set()
    assignment = dict()
    for clause in cnf.clauses:
        for literal in clause.literals:
            unused_variables.add(literal.variable)

    while len(unused_variables) != 0 and len(cnf.clauses) != 0:
        cnf = saturate(cnf)

        is_assignment_found = False
        for clause in cnf.clauses:
            if len(clause.literals) == 1:
                is_assignment_found = True
                literal = tuple(clause.literals)[0]
                assignment[literal.variable] = not literal.add_negation
                unused_variables.remove(literal.variable)
        if not is_assignment_found:
            variable = unused_variables.pop()
            assignment[variable] = False

        cnf.add_assignment(assignment)

    for variable in unused_variables:
        assignment[variable] = False
    return assignment


sat_assignment("(~p \\/ q) /\\ (~p \\/ r) /\\ (~q \\/ r) /\\ (p \\/ ~q) /\\ (~p \\/ ~q) /\\ (~p \\/ ~r)")
