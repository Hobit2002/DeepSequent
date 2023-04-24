import itertools
from connectives import *
from axioms import Axiom

class State():
    
    def __init__(self,*args,deterministic=True) -> None:
        self.formulas = list(args)
        self.successors = []
        self.deterministic = deterministic

    def possibleActions(self):
        possible_actions = []
        # Loop all actions and decide, whether they are applicable
        for action in Action.__subclasses__():
            if action.applicable(self):possible_actions.append(action)
        # Return list of applicable actions
        return possible_actions

    def applyAction(self,action):
        # Copy the given state and create a new one with the same formulas
        new_state = action(State(*self.formulas))
        return new_state

    def fitAxioms(self):
        # Get all axioms and check if any of them is applicable
        for axiom in Axiom.__subclasses__():
            check_result = axiom.check(self)
            # If true, return identity of the axiom
            if check_result:return check_result
        # Otherwise return false
        else: return False

    def __str__(self) -> str:
        # Get string versions of all assumption formulas
        str_formulas = [str(formula) for formula in self.formulas[:-1]]
        # Sort them
        str_formulas.sort()
        # Create a string representation of assumption
        str_rep = ""
        for formula in str_formulas: str_rep += f";{formula}"
        # Create a string representation of the whole state
        return f"{str_rep[1:]} ==> {str(self.formulas[-1])}"

    def __hash__(self) -> int:
        try:
            to_return = hash(str(self))
        except RecursionError:
            to_return = hash("This is too complex to be the right way")
        return to_return

# Actions

class Action():

    @staticmethod
    def applicable(state:State) -> bool:
        return False
    
    @staticmethod
    def recursive_replacement(formula:Connective,replace_dict:dict,formula_replacement:bool = False) -> Connective:
        # Get all successors of the given connective
        successors = [formula.successor] if isinstance(formula,Quantifier) else [formula.operand] if isinstance(formula,Not) else formula.operands
        # Loop the successors
        for s,successor in enumerate(successors):
            # If the successor is a literal with value contained in replace_dict, replace it
            # Check, if the value is literal
            if isinstance(successor,Literal):
                if successor.value in replace_dict.keys():
                    # If formula_replacement is set to true, exchange literals in current connective for given objects 
                    if formula_replacement:
                        if isinstance(formula,Not):
                            formula.operand = replace_dict[successor.value]
                        else:
                            formula.operands[s] = replace_dict[successor.value]
                    # Otherwise just change the literal value
                    else:
                        successors[s].value = replace_dict[successor.value].value
            # If the value is not literal, call recursive_replacement on it
            else:
                Action.recursive_replacement(successor,replace_dict,formula_replacement=formula_replacement)

    @staticmethod
    def instantiates():
        return False
             
# Negation rules

class EliminateDoubleNegation(Action):

    @staticmethod
    def applicable(state:State) -> list:
        possible_sequents = []
        for f,formula in enumerate(state.formulas):
            if isinstance(formula,Not) and isinstance(formula.operand,Not):
                possible_sequents.append(f)
        return possible_sequents

    @staticmethod
    def apply(state:State,formula:int) -> State:
        negations = 2
        cursor = state.formulas[formula].operand.operand
        # Loop operands until you find a non-Not one
        while isinstance(cursor, Not):
            negations += 1
            cursor = cursor.operand
        # Return the state with given formula negated at most once
        state.formulas[formula] = Not(cursor) if negations % 2 else cursor
        return state

class NegateGoal(Action):

    @staticmethod
    def applicable(state:State) -> list:
        # Check that goal is not a false constant
        if state.formulas[-1] != Or():
            return [len(state.formulas) - 1]
        else:return []

    @staticmethod
    def apply(state:State,formula:int) -> State:
        state.formulas[-1] = Not(state.formulas[-1])
        state.formulas.append(Or())
        return state
    
class NegateSequent(Action):

    @staticmethod
    def applicable(state:State) -> list:
        # Check that goal is a false constant
        if state.formulas[-1] == Or():
            return [i for i in range(len(state.formulas) - 1)]
        else:return []

    @staticmethod
    def apply(state:State,formula:int) -> State:
        # Set goal of state to the negation of given sequent
        state.formulas[-1] = Not(state.formulas[formula])
        # If there were multiple formulas in assumption, delete the negated one
        if len(state.formulas) - 2: del state.formulas[formula]
        # Otherwise insert true constant into assumption
        else: state.formulas[formula] = And()
        return state

# De Morgan laws
class DeMorganAbstract(Action):

    @staticmethod
    def checkApplicability(state:State,from_class:type):
        possible_sequents = []
        # Check that there is a negation of given connective among the formulas
        for f,formula in enumerate(state.formulas):
            if isinstance(formula,Not) and isinstance(formula.operand,from_class):
                possible_sequents.append(f)
        return possible_sequents
    
    @staticmethod
    def apply(state:State,to_class:type,formula:int):
        state.formulas[formula] = to_class(*[Not(operand) for operand in state.formulas[formula].operand.operands])
        return state

class DeMorganAnd(Action):

    @staticmethod
    def applicable(state:State) -> list:
        return DeMorganAbstract.checkApplicability(state,And)            

    @staticmethod
    def apply(state:State,formula:int) -> State:
        return DeMorganAbstract.apply(state,Or,formula)
    
class DeMorganOr(Action):

    @staticmethod
    def applicable(state:State) -> list:
        return DeMorganAbstract.checkApplicability(state,Or)            

    @staticmethod
    def apply(state:State,formula:int) -> State:
        return DeMorganAbstract.apply(state,And,formula)
    
class DeMorganExistential(Action):

    @staticmethod
    def applicable(state:State) -> list:
        return DeMorganAbstract.checkApplicability(state,Existential)            

    @staticmethod
    def apply(state:State,formula:int) -> State:
        variables = state.formulas[formula].operand.variables
        state.formulas[formula] = Universal(*variables,successor = Not(state.formulas[formula].operand.successor))
        return state
        #return DeMorganAbstract.apply(state,Universal,formula)

class DeMorganUniversal(Action):

    @staticmethod
    def applicable(state:State) -> list:
        return DeMorganAbstract.checkApplicability(state,Universal)            

    @staticmethod
    def apply(state:State,formula:int) -> State:
        variables = state.formulas[formula].operand.variables
        state.formulas[formula] = Existential(*variables,successor = Not(state.formulas[formula].operand.successor))
        return state
        #return DeMorganAbstract.apply(state,Existential,formula)

# Quantifier replacement rules
class QuantifierReplacementAbstract(Action):

    @staticmethod
    def checkApplicability(state:State,from_class:type):
        possible_sequents = []
        # Get all occurences of given  quantifier among states of the formula
        for f,formula in enumerate(state.formulas):
            if isinstance(formula,from_class):
                possible_sequents.append(f)
        return possible_sequents
    
    @staticmethod
    def apply(state:State,to_class:type,formula:int):
        new_state = State(*state.formulas)
        # Get variables bounded by the quantifier
        variables = state.formulas[formula].variables
        # Get all combinations of those variables that could be true
        true_assignments = []
        for true_count in range(len(variables)):
            true_assignments += itertools.combinations(variables,true_count)
        # Loop those combination and replace variables in successor formula with corresponding truth constants
        operands = []
        # Loop combinations
        for true_assignment in true_assignments:
            # Assign true constant to varibles contained in the combination and false to the rest
            replace_dict = {var:And() if var in true_assignment else Or() for var in variables}
            # Add successor formula with bounded variables to be replaced by truth constants
            operands.append(Action.recursive_replacement(new_state.formulas[formula].successor,replace_dict,formula_replacement = True))
        # Create a new connective with previous combinations as its operands
        state.formulas[formula] = to_class(*operands)
        return state

class ExistentialReplacement(Action):
    
    @staticmethod
    def applicable(state:State) -> list:
        return QuantifierReplacementAbstract.checkApplicability(state,Existential)

    @staticmethod
    def apply(state:State,formula:int) -> State:
        return QuantifierReplacementAbstract.apply(state,Or,formula)

class ExistentialReplacement(Action):
    
    @staticmethod
    def applicable(state:State) -> list:
        return QuantifierReplacementAbstract.checkApplicability(state,Universal)

    @staticmethod
    def apply(state:State,formula:int) -> State:
        return QuantifierReplacementAbstract.apply(state,And,formula)

# Assumption rules
class AssumptionAbstract(Action):

    @staticmethod
    def checkApplicability(state:State,subclass:type) -> list:
        possible_sequents = []
        # Check if the given connective is present in assumption
        for f,formula in enumerate(state.formulas[:-1]):
            if isinstance(formula,subclass):
                possible_sequents.append(f)
        return possible_sequents
 
class AndAssumption(Action):

    @staticmethod
    def applicable(state:State) -> list:
        return AssumptionAbstract.checkApplicability(state,And)

    @staticmethod
    def apply(state:State,formula:int) -> State:
        operands = state.formulas[formula].operands
        del state.formulas[formula]
        for operand in operands: state.formulas.insert(0,operand)
        return state

class OrAssumption(Action):

    @staticmethod
    def applicable(state:State) -> list:
        return AssumptionAbstract.checkApplicability(state,Or)

    @staticmethod
    def apply(state:State,formula:int) -> State:
        operands = state.formulas[formula].operands
        formulas = state.formulas
        to_return = []
        # For each operand of the selected formula, create a new branch with this operand replacing original formula
        for operand in operands:
            new_formulas = formulas.copy()
            new_formulas[formula] = operand            
            to_return.append(State(*new_formulas))
        return to_return

class XorAssumption(Action):

    @staticmethod
    def applicable(state:State) -> list:
        return AssumptionAbstract.checkApplicability(state,Xor)

    @staticmethod
    def apply(state:State,formula:int) -> State:
        operands = state.formulas[formula].operands
        formulas = state.formulas
        to_return = []
        # For each operand of the given formula, create a new branch, where this operand is as it is and others are negated
        for o1,operand in enumerate(operands):
            # Add non-negated operand
            new_formulas = formulas.copy()
            new_formulas[formula] = operand
            # Add negated operands
            for o2,neg_operand in enumerate(operands):
                if o1 != o2: new_formulas.insert(0,Not(neg_operand))          
            to_return.append(State(*new_formulas))
        return to_return

class UniversalAssumption(Action):

    @staticmethod
    def applicable(state:State) -> list:
        return AssumptionAbstract.checkApplicability(state,Universal)

    @staticmethod
    def apply(state:State,formula:int,replace_dict) -> State:
        new_state = State(*state.formulas)
        # Replace the universal quantifier in the assumption by its successor formula.
        new_state.formulas[formula] = new_state.formulas[formula].successor
        # Replace variables in this successor formula by the corresponding value from the replace_dict
        Action.recursive_replacement(new_state.formulas[formula],replace_dict)
        return new_state
    
    @staticmethod
    def getAssignments(state:State,formula:int):
        assignments = []
        variables = state.formulas[formula].variables
        # Get variables bounded in the successor formula
        successor_bounded = state.formulas[formula].successor.getBoundedLiterals()
        # Get all variables which can be used for assignment. Exclude those bounded by the quantifier or by its successors.
        possible_assignment = set(Literal.used_tokens) - set(variables + successor_bounded)
        # Get all possible assignments of quantifier bounded variables
        for key_combination in itertools.permutations(variables):
            for assignment in itertools.combinations(possible_assignment,len(variables)):
                # Add the assignment to the list
                assignments.append({key_combination[i]:assignment[i] for i in range(len(variables))})
        return assignments
    
    @staticmethod
    def instantiates():
        return True

class ExistentialAssumption(Action):

    @staticmethod
    def applicable(state:State) -> list:
        return AssumptionAbstract.checkApplicability(state,Existential)

    @staticmethod
    def apply(state:State,formula:int) -> State:
        new_state = State(*state.formulas)
        # Create skolemn variables as a replacement for those bounded by the quantifier
        replace_dict = {var:Literal.get_new(skolemn=True) for var in new_state.formulas[formula].variables}
        # Replace the existential quantifier in the assumption by its successor formula.
        new_state.formulas[formula] = new_state.formulas[formula].successor
        # Replace variables in this successor formula by the corresponding value from the replace_dict
        Action.recursive_replacement(new_state.formulas[formula],replace_dict)
        return new_state

# Goal rules
class GoalAbstract(Action):

    @staticmethod
    def checkApplicability(state:State,subclass:type) -> list:
        if isinstance(state.formulas[-1],subclass) and (isinstance(state.formulas[-1],Quantifier) or len(state.formulas[-1].operands)) :return [len(state.formulas)-1]
        else: return []

class AndGoal(Action):

    @staticmethod
    def applicable(state:State) -> list:
        return GoalAbstract.checkApplicability(state,And)

    @staticmethod
    def apply(state:State,formula:int) -> State:
        operands = state.formulas[formula].operands
        formulas = state.formulas
        to_return = []
        # For each operand, create a new branch with this operand as its goal
        for operand in operands:
            new_formulas = formulas.copy()
            new_formulas[formula] = operand            
            to_return.append(State(*new_formulas))
        return to_return

class OrGoal(Action):

    @staticmethod
    def applicable(state:State) -> list:
        return GoalAbstract.checkApplicability(state,Or)

    @staticmethod
    def apply(state:State,formula:int) -> State:
        operands = state.formulas[formula].operands
        formulas = state.formulas
        to_return = []
        # For each operand, create a new branch with this operand as its goal
        for operand in operands:
            new_formulas = formulas.copy()
            new_formulas[formula] = operand
            # Set those new branches as indeterministic            
            to_return.append(State(*new_formulas, deterministic= False))
        return to_return

class XorGoal(Action):

    @staticmethod
    def applicable(state:State) -> list:
        return GoalAbstract.checkApplicability(state,Xor)

    @staticmethod
    def apply(state:State,formula:int) -> State:
        # Create two new branches corresponding to moving negated xor to assumption
        xor = state.formulas[formula]
        state.formulas[formula] = Or()
        return [State(*xor.successors,*state.operands),State(Or(*xor.successors),*state.operands)]

class UniversalGoal(Action):

    @staticmethod
    def applicable(state:State) -> list:
        return GoalAbstract.checkApplicability(state,Universal)

    @staticmethod
    def apply(state:State,formula:int) -> State:
        new_state = State(*state.formulas)
        # Create skolemn variables as a replacement for those bounded by the quantifier
        replace_dict = {var:Literal.get_new(skolemn=True) for var in new_state.formulas[formula].variables}
        # Replace the universal quantifier in the assumption by its successor formula.
        new_state.formulas[formula] = new_state.formulas[formula].successor
        # Replace variables in this successor formula by the corresponding value from the replace_dict
        Action.recursive_replacement(new_state.formulas[formula],replace_dict)
        return new_state

class ExistentialGoal(Action):

    @staticmethod
    def applicable(state:State) -> list:
        return GoalAbstract.checkApplicability(state,Existential)

    @staticmethod
    def apply(state:State,formula:int,replace_dict) -> State:
        new_state = State(*state.formulas)
        new_state.formulas[formula] = new_state.formulas[formula].successor
        Action.recursive_replacement(new_state.formulas[formula],replace_dict)
        return new_state
        
    @staticmethod
    def instantiates():
        return True
    
    @staticmethod
    def getAssignments(state:State,formula:int):
        assignments = []
        variables = state.formulas[formula].variables
        # Get variables bounded in the successor formula
        successor_bounded = state.formulas[formula].successor.getBoundedLiterals()
        # Get all variables which can be used for assignment. Exclude those bounded by the quantifier or by its successors.
        possible_assignment = set(Literal.used_tokens) - set(variables + successor_bounded)
        # Get all possible assignments of quantifier bounded variables
        for key_combination in itertools.permutations(variables):
            for assignment in itertools.combinations(possible_assignment,len(variables)):
                # Add the assignment to the list
                assignments.append({key_combination[i]:assignment[i] for i in range(len(variables))})
        return assignments