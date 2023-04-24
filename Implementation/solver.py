from formula_parser import parse
from rules import State, EliminateDoubleNegation,NegateSequent
from connectives import Literal, Not
import random

transposition_table = {}

# Define different solving approaches

# Solve by brute force - the only one so far 
def brute_force(state):
    proof = str(state)

    #  **** DOES THE STATE FIT THE AXIOMS? **** 
    # Check whether the given state already fit axioms
    fiting_axiom = state.fitAxioms()
    # If true, return the state together with fulfilled axiom
    if fiting_axiom:
        return f"{proof}\n{fiting_axiom}"
    # If not, save the current state to transpostition table as 'yet unsolved'
    transposition_table[hash(state)] = ""


    #  **** GET ALL POSSIBLE ACTIONS **** 
    # Get all applicable actions and shuffle them
    possible_actions = state.possibleActions()
    random.shuffle(possible_actions)

    # Some heuristics needed to make brute force at least somewhat useful
    # Heuristics: if possible, eliminate double negation
    if EliminateDoubleNegation in possible_actions:
        possible_actions.insert(0, possible_actions.pop(possible_actions.index(EliminateDoubleNegation)))
    # Heuristics: sequent negation is the least preferred operation
    if NegateSequent in possible_actions:
        possible_actions.remove(NegateSequent)
        nonliteral_knowledge = False
        # And is forbidden, if there are only (negated) literals in the knowledge base
        for formula in state.formulas[:-1]:
            if not isinstance(formula,Literal) and (not isinstance(formula,Not) or (not isinstance(formula.operand, Literal) and not isinstance(formula.operand, Not))):
                nonliteral_knowledge = True
                break
        if nonliteral_knowledge:possible_actions.append(NegateSequent)

    #  **** APPLY ACTIONS ****
    # Loop actions
    for action in possible_actions:
        # For each action, get indices of sequents where it can be applied
        sequents = action.applicable(state)
        # Apply action on every possible sequent
        for sequent in sequents:
            try:
                # In case of ExistentialGoal or UniversalAssumption, apply the action for each possible instantiation
                if action.instantiates():
                    # Get all possible instantiations
                    assignments = action.getAssignments(State(*state.formulas),sequent)
                    # Apply all possible instantiations
                    result = []
                    for replace_dict in assignments: result += action.apply(State(*state.formulas),sequent,replace_dict) 
                # Otherwise simply apply the action
                else: result = action.apply(State(*state.formulas),sequent)
            # If a recursion error occurs during action aplication, continue to the next sequent
            except RecursionError:
                print("Reccursion error occured")
                continue
            # If application of action resulted into list of states, loop it
            if type(result) == list:
                # If the list is empty, continue to the next sequent
                if not len(result):continue
                # Otherwise start looping
                prooflist = []
                for res_state in result:
                    # If the resulting state was already found, get its result from the transposition table
                    if hash(res_state) in transposition_table.keys():
                        subproof = transposition_table[hash(res_state)]
                    # Otherwise apply brute_force recursively to it
                    else:
                        try:
                            subproof = brute_force(res_state)
                        # If a recursion error occurs, return "Proof not found"
                        # We are not searching further, because any other brute_dorce call would cause the same
                        except RecursionError:
                            return ""
                    # If a proof for the branch was found and the action is indeterministic, return the proof
                    if subproof and not res_state.deterministic:
                        proof = f"{proof}\n{action.__name__}:\n{subproof}"
                        transposition_table[hash(state)] = proof
                        return proof
                    # If a proof for the branch was not found and the action is deterministic stop looping the sequents
                    elif not subproof and res_state.deterministic:break
                    # Otherwise, save the proof
                    prooflist.append(subproof)
                # If the action is deterministc and proofs were found for all its branches, combine those proofs and return them
                else:
                    if res_state.deterministic:
                        subproof = ""
                        # Combine the proofs
                        for b,branch in enumerate(prooflist):
                            subproof += f"\nBranch {b}:"
                            subproof += ("\n"+branch).replace("\n","\n  ")
                        proof = f"{proof}\n{action.__name__}:{subproof}"
                        # Add the found proof to the transposition table
                        transposition_table[hash(state)] = proof 
                        # Return the proof 
                        return proof
            # If application of action resulted into a single state, inspect it
            else:
                # If the resulting state was already found, get its result from the transposition table
                if hash(result) in transposition_table.keys():
                    subproof = transposition_table[hash(result)]
                # Otherwise apply brute_force recursively to it
                else:
                    try:
                        subproof = brute_force(result)
                    except RecursionError:
                        return ""
                # If the proof of resulting state was found, return it
                if subproof: 
                    proof = f"{proof}\n{action.__name__}:\n{subproof}"
                    # Update the entry in the transposition table
                    transposition_table[hash(state)] = proof
                    return proof

    # If no of the actions resulted into proof, return "proof not found" 
    return ""

# Parse the given file 
state = parse(input("File directory:"))
# Find proof via brute force
proof = brute_force(state)
# Print the result
print(proof if proof else "Proof not found")

