from connectives import Or,Not

class Axiom:
    pass

class GoalAssumption(Axiom):
    
    @staticmethod
    def check(state):
        for formula in state.formulas[:-1]:
            if formula == state.formulas[-1]:
                return "Goal in assumption"
        return False

class ContradictionAssumption(Axiom):
    
    @staticmethod
    def check(state):
        for formula in state.formulas[:-1]:
            if formula == Or() or Not(formula) in state.formulas[:-1]:
                return "Contradiction in assumption"
        return False
