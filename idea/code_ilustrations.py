
# Algorithm: Brute force search

# Data:Graph node
# Return: proof found ? True : False
def brute_force(node):
    for action in node.possibleActions():
        succesor_state = node.applyAction(action)
        if succesor_state.fitAxioms():
            return True
        else:
            succesor_result = brute_force(succesor_state)
            if succesor_result: return True
    return False

# Algorithm: Selective search

# Data:Graph node
# Return: proof found ? True : False
def selective_search(node):
    succesor_states = list()
    for action in node.possibleActions():
        succesor_states.append(node.applyAction(action))
    succesor_states.sort(key= lambda node:node.evaluate())
    for succesor in succesor_states[-2:]:
        if succesor.fitAxioms():
            return True
        else:
            succesor_result = selective_search(succesor)
            if succesor_result: return True
    return False
    
# Algorithm: Reinforcement solver with a single "attention-slot"

# Data:Graph node
# Return: proof found ? True : False
def reinforcement_single(node):
    if node.fitAxioms():
        return True
    actions = node.possibleActions()
    if actions.length == 0:
        return False
    selected_action = actions.choose_stochastically(key = lambda action: action.evaluate())
    return reinforcement_single(node.applyAction(selected_action))

# Algorithm: Reinforcement solver able to follow multiple branches

# Data:Graph node
# Return: proof found ? True : False
def reinforcement_tree_search(node):
    if node.fitAxioms():
        return True
    actions = node.possibleActions()
    if actions.length == 0:
        return False
    actions.sort(key = lambda action: action.evaluate())
    for action in actions[-2:]:
        if reinforcement_tree_search(node.applyAction(action)):
            return True
    return False 