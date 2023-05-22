import torch, random
import numpy as np
from task_generator import generate_formula
from rules import *

class RLModel(torch.nn.Module):
    
    def __init__(self) -> None:
        super().__init__()
        self.lstm1 = torch.nn.LSTM(11, 70)
        self.ac1 = torch.nn.ReLU()
        self.fcn2 = torch.nn.Linear(88, 1)
        self.action_list = [NegateGoal, NegateSequent, DeMorganAnd, DeMorganOr, DeMorganExistential,
               DeMorganUniversal, ExistentialReplacement, UniversalReplacement,
                AndAssumption, OrAssumption, XorAssumption, UniversalAssumption,
                ExistentialAssumption, AndGoal, OrGoal, XorGoal, UniversalGoal, ExistentialGoal]

    def forward(self, x: torch.Tensor, given_action) -> torch.Tensor:
        x = self.lstm1(x)[1][0].squeeze()
        x = self.ac1(x)
        selected_action = torch.tensor([given_action is action for action in self.action_list]).to(torch.float32)
        with_actions = torch.cat([x,selected_action]) 
        return self.fcn2(with_actions)
    
def feedback(optimizer, expected, recieved):
    optimizer.zero_grad()
    print(f"Expected:{expected[0][0]:.3f} Recieved:{recieved:.3f}")
    criterion = torch.nn.SmoothL1Loss()
    received_tensor = torch.tensor(recieved, requires_grad=True)
    expected_tensor = torch.tensor(expected, requires_grad=True).unsqueeze(1)
    loss = criterion(received_tensor, expected_tensor)
    loss.backward()
    optimizer.step()

transposition_table = {}
action_list = [NegateGoal, NegateSequent, DeMorganAnd, DeMorganOr, DeMorganExistential,
               DeMorganUniversal, ExistentialReplacement, UniversalReplacement,
                AndAssumption, OrAssumption, XorAssumption, UniversalAssumption,
                ExistentialAssumption, AndGoal, OrGoal, XorGoal, UniversalGoal, ExistentialGoal]


# Solve by brute force - the only one so far 
def reinforcement_tree_search(state):
    proof = str(state)
    #  **** DOES THE STATE FIT THE AXIOMS? **** 
    # Check whether the given state already fit axioms
    fiting_axiom = state.fitAxioms()
    # If true, return the state together with fulfilled axiom
    if fiting_axiom:
        print(f"{fiting_axiom}")
        return f"{proof}\n{fiting_axiom}"
    # If not, save the current state to transpostition table as 'yet unsolved'
    transposition_table[hash(state)] = ""


    #  **** GET ALL POSSIBLE ACTIONS **** 
    # Get all applicable actions and usinf the RL model select at most 3 most promising
    possible_actions = state.possibleActions()
    qualities = np.array([state.model(torch.tensor(state.embedde()).to(torch.float32), action).detach().numpy() for action in possible_actions])
    prefered_indexes = np.argsort(qualities)
    chosen_actions = []
    for i in range(min([3, len(possible_actions)])):
        pref_index = prefered_indexes[i][0]
        chosen_actions.append(action_list[pref_index])

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
    for a,action in enumerate(possible_actions):
        predicted_quality = qualities[prefered_indexes[a]]
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
                    for replace_dict in assignments: 
                        result.append(action.apply(State(*state.formulas,deterministic = False),sequent,replace_dict)) 
                    # Set 
                # Otherwise simply apply the action
                else: 
                    result = action.apply(State(*state.formulas),sequent)
                    if isinstance(result,State):
                        for f,formula in enumerate(result.formulas):
                            result.formulas[f] = EliminateDoubleNegation.cursorize(formula)
                            formula = result.formulas[f]
                            if isinstance(formula, BinaryGate):
                                for o, operand in enumerate(formula.operands):
                                    formula.operands[o] = EliminateDoubleNegation.cursorize(operand)
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
                            subproof = reinforcement_tree_search(res_state)
                        # If a recursion error occurs, return "Proof not found"
                        # We are not searching further, because any other brute_dorce call would cause the same
                        except RecursionError:
                            return ""
                    # If a proof for the branch was found and the action is indeterministic, return the proof
                    if subproof and not res_state.deterministic:
                        feedback(state.optimizer,predicted_quality,1/np.log10(len(subproof)))
                        proof = f"{proof}\n{action.__name__}:\n{subproof}"
                        transposition_table[hash(state)] = proof
                        return proof
                    # If a proof for the branch was not found and the action is deterministic stop looping the sequents
                    elif not subproof and res_state.deterministic:
                        feedback(state.optimizer,predicted_quality,-1.0)
                        break
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
                        feedback(state.optimizer,predicted_quality,1/np.log10(len(subproof)))
                        # Add the found proof to the transposition table
                        transposition_table[hash(state)] = proof 
                        # Return the proof 
                        return proof
                    else: feedback(state.optimizer,predicted_quality,-1.0)
            # If application of action resulted into a single state, inspect it
            else:
                # If the resulting state was already found, get its result from the transposition table
                if hash(result) in transposition_table.keys():
                    subproof = transposition_table[hash(result)]
                    if not subproof and action is EliminateDoubleNegation: return ""
                # Otherwise apply brute_force recursively to it
                else:
                    try:
                        subproof = reinforcement_tree_search(result)
                    except RecursionError:
                        return ""
                # If the proof of resulting state was found, return it
                if subproof:
                    feedback(state.optimizer,predicted_quality,1/np.log10(len(subproof))) 
                    proof = f"{proof}\n{action.__name__}:\n{subproof}"
                    # Update the entry in the transposition table
                    transposition_table[hash(state)] = proof
                    return proof
                else:
                    feedback(state.optimizer,predicted_quality,-1.0)

    # If no of the actions resulted into proof, return "proof not found" 
    return ""

model = RLModel()
State.model = model
State.optimizer = torch.optim.Adam(model.parameters(), lr=1e-2)

criterion = torch.nn.CrossEntropyLoss()

go = True
while go:
    state = generate_formula(int(input("What should be the formula complexity? ")))
    print(state)
    steps = 0
    transposition_table = {}
    reinf_solution = reinforcement_tree_search(state)
    print(f"Conclusion: {bool(reinf_solution)}")
    go = input("Should I continue (do not type anything if not)? ")
