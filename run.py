
from bauhaus import Encoding, proposition, constraint, Or, And
from bauhaus.utils import count_solutions, likelihood
from itertools import product, combinations
import random
# These two lines make sure a faster SAT solver is used.
from nnf import config
config.sat_backend = "kissat"

#----------------Constants-----------------
RANKS = (1,2,3,4,5,6,7,8,9) # tuple: ordered and unchangable data structure
SUITS = ('A', 'B', 'C', 'D')
NUM_OF_CARDS = 10
#-------------Global Variables-------------
global deck, discard, player_cards, opponent_cards, deck_index

# Encoding that will store all of your constraints
E = Encoding()

class Hashable: #recommanded
    def __hash__(self):
        return hash(str(self))

    def __eq__(self, __value: object) -> bool:
        return hash(self) == hash(__value)

    def __repr__(self):
        return str(self)
 # To create propositions, create classes for them first, annotated with "@proposition" and the Encoding   
@proposition(E)
class Player(Hashable):
    def __init__(self, rank: int, suit: str):
        self.a = rank
        self.b = suit

    def __str__(self):
        return f"P({self.a}{self.b})"
    
@proposition(E)
class Opponent(Hashable):
    def __init__(self, rank: int, suit: str):
        self.a = rank
        self.b = suit

    def __str__(self):
        return f"O({self.a}{self.b})"
    
@proposition(E)
class Pl_run(Hashable):
    def __init__(self, related_cards):
        self.related_run_cards = related_cards

    def __str__(self):
        return f"player_run_[{self.related_run_cards}]"

@proposition(E)
class Pl_set(Hashable):
    def __init__(self, rank: int, suit: str):
        self.rank = rank
        self.excluded_suit = suit

    def __str__(self):
        return f"player_set_{self.rank}_{self.excluded_suit}"
    
@proposition(E)
class Pl_want(Hashable):
    def __init__(self, rank: int, suit: str):
        self.a = rank
        self.b = suit

    def __str__(self):
        return f"player_want_{self.a}{self.b}"

@proposition(E)
class Opp_pick(Hashable):
    def __init__(self, rank: int, suit: str):
        self.a = rank
        self.b = suit
    
    def __str__(self):
        return f"opp_pick_{self.a}{self.b}"

@proposition(E)
class Opp_discard(Hashable):
    def __init__(self, rank: int, suit: str):
        self.a = rank
        self.b = suit
    
    def __str__(self):
        return f"opp_discard_{self.a}{self.b}"
    
# Helper functions:
def cards_to_rank_dict(my_cardlist: list) -> dict:
    '''Takes in a list my_cardlist, returns the dictionary that maps every rank in the list into a set of suits'''
    my_dict = {} # dictionary that maps the ranks into a set of suits, eg. {1:{'A', 'B'}, 3:{'C','A'}}
    for x in my_cardlist:
        if x[0] in my_dict:
            my_dict[x[0]].add(x[1])
        else:
            my_dict[x[0]] = {x[1]}
    return my_dict

def cards_to_suit_dict(my_cardlist: list) -> dict:
    '''Takes in a list my_cardlist, returns the dictionary that maps every rank in the list into a set of suits'''
    my_dict = {} # dictionary that maps the ranks into a set of suits, eg. {1:{'A', 'B'}, 3:{'C','A'}}
    for x in my_cardlist:
        if x[1] in my_dict:
            my_dict[x[1]].add(x[0])
        else:
            my_dict[x[1]] = {x[0]}
    return my_dict

def initial_game() -> None :
    # reset the two global variable and create a shuffled deck
    global deck, player_cards, opponent_cards, deck_index
    global discard
    discard = []
    deck = list (product (RANKS, SUITS))
    random.shuffle(deck)
    # distribute cards to the player and opponent
    player_cards = deck[:NUM_OF_CARDS]
    opponent_cards = deck[NUM_OF_CARDS:NUM_OF_CARDS*2]
    deck_index = NUM_OF_CARDS*2
    # deck = deck[NUM_OF_CARDS*2:]
    # print("deck:", deck)
    # print(player_cards)
    # print(opponent)

def remove_card_from_list(cards: list, remove_items, rank: int, suit: str) -> list:
    if rank == None:
        for target in remove_items:
            cards.remove((target, suit))
    else:
        for target in remove_items:
            cards.remove((rank, target))
    return cards # updated card list that removes the target items

def meld_list_generator(remaining_cards:list) -> list:
    '''
    Takes in a list of cards, find all the existing melds and potential melds
    Return a list of three lists: [existing_meld_list, remaining_cards, potential_meld_list]
    '''
    existing_meld_list = []
    potential_meld_list = []
    # print('input cards:', remaining_cards)
    # search for RUNS
    cards_in_suit = cards_to_suit_dict(remaining_cards)
    for el_suit, el_rank_set in cards_in_suit.items():
        if(len(el_rank_set)>2):
            temp_list = sorted(list(el_rank_set))
            num_of_con_term = 1
            from_index = 0
            for index in range (len(temp_list)):
                if index == len(temp_list)-1: # check if the last element counts towards a run
                    if ((temp_list[index-1]+1) == temp_list[index]):
                        existing_meld_list.append((el_suit,temp_list[from_index:index+1]))                        
                        remaining_cards = remove_card_from_list(remaining_cards, temp_list[from_index:index+1], None, el_suit)
                elif ((temp_list[index]+1) != temp_list[index+1]): # if the two cards are NOT consecutive
                    if num_of_con_term >2: # if the previous cards makes a run, add them into the existing_meld
                        existing_meld_list.append((el_suit,temp_list[from_index:index+1]))
                        remaining_cards = remove_card_from_list(remaining_cards, temp_list[from_index:index+1], None, el_suit)
                        from_index = index + 1
                    num_of_con_term = 1
                elif ((temp_list[index]+1) == temp_list[index+1]): # if the two cards are consecutive
                    num_of_con_term +=1 
        # FIXME: find potential melds for runs
    # search for SETS
    cards_in_rank = cards_to_rank_dict(remaining_cards)
    for el_rank, el_suit_set in cards_in_rank.items():
        if (len(el_suit_set)>2):
            existing_meld_list.append((el_rank, el_suit_set))
            remaining_cards = remove_card_from_list(remaining_cards, list(el_suit_set), el_rank, None)
        elif (len(el_suit_set)>1):
            potential_meld_list.append((el_rank, el_suit_set))
            remaining_cards = remove_card_from_list(remaining_cards, list(el_suit_set), el_rank, None)
    # print('existing melds:', existing_meld_list)
    # print('potential melds:', potential_meld_list)
    # print('remaining cards:', remaining_cards)
    return existing_meld_list, remaining_cards, potential_meld_list

# Different classes for propositions are useful because this allows for more dynamic constraint creation
# for propositions within that class. For example, you can enforce that "at least one" of the propositions
# that are instances of this class must be true by using a @constraint decorator.
# other options include: at most one, exactly one, at most k, and implies all.
# For a complete module reference, see https://bauhaus.readthedocs.io/en/latest/bauhaus.html


# Build an example full theory for your setting and return it.
#
#  There should be at least 10 variables, and a sufficiently large formula to describe it (>50 operators).
#  This restriction is fairly minimal, and if there is any concern, reach out to the teaching staff to clarify
#  what the expectations are.
def example_theory():
    # INITIALIZE VARIABLES for the game
    global player_cards, opponent_cards, deck_index
    initial_game()
    opp_pick_card =  deck[deck_index]
    deck_index +=1 
    opponent_cards.append(opp_pick_card)
    # Opponent: randomly pick a card to discard from the cards that does not make a meld
    opp_discard_list = meld_list_generator(list(opponent_cards))[1] # the remaining cards
    opp_discard_card = None
    if len(opp_discard_list)>0:
        opp_discard_card = opp_discard_list[random.randint(0,len(opp_discard_list)-1)]
        opponent_cards.remove(opp_discard_card)
    
    pl_cards_dict = cards_to_rank_dict(sorted(player_cards)) # pl_card_dict = {1:{'A','B'}, ....}
    print('player cards: ', pl_cards_dict)
    # print('opponent cards:', opponent_cards) 
    print('opponent pick up:', opp_pick_card)
    print('opponent discard:', opp_discard_card)
    # Add custom constraints by creating formulas with the variables you created. 
    #-------------------------------------------------------------------------------------------------------
    # CONSTRAINT: If the card is in player card list, then the player must have that card
    #             If player has card(a,b), then Opponent does not have card(a,b)
    #-------------------------------------------------------------------------------------------------------
    for card in player_cards:
        E.add_constraint(Player(card[0], card[1]))
        E.add_constraint(Player(card[0], card[1]) >> ~Opponent(card[0], card[1]))
    #-------------------------------------------------------------------------------------------------------
    # CONSTRAINT: check in player_cards for SETS
    #-------------------------------------------------------------------------------------------------------
    for el_set in pl_cards_dict.items():
        if (len(el_set[1])>2):
            excl_suit_list = list(set(SUITS).difference(el_set[1]))
            excl_suit = 'Z'
            if len(excl_suit_list)>0:
                excl_suit = excl_suit_list[0]
            # print("there exist a set", el_set, "with exclude: ", excl_suit)
            E.add_constraint(Pl_set(el_set[0], excl_suit))

    #-------------------------------------------------------------------------------------------------------
    # CONSTRAINT: check in player_cards for RUNS
    #-------------------------------------------------------------------------------------------------------
    # BUG: data access error, note that pl_card_dict has key = rank, value = set of the suits
    # is_consecutive = all(pl_cards_dict[i] == pl_cards_dict[i-1] + 1 for i in range(1, len(pl_cards_dict)))  
    # print(is_consecutive)

    #-------------------------------------------------------------------------------------------------------
    # CONSTRAINT: If opponent picks a card of “a” rank and “b” suit, then opponent has that card:
    #-------------------------------------------------------------------------------------------------------
    if opp_pick_card == None:
        E.add_constraint(~Opponent(opp_pick_card[0], opp_pick_card[1]))
    else:
        E.add_constraint(Opponent(opp_pick_card[0], opp_pick_card[1]))

    #-------------------------------------------------------------------------------------------------------
    # CONSTRAINT: If the opponent picks a card of “a” rank and “b” suit, that card must create a meld or contribute to an existing meld.
    #-------------------------------------------------------------------------------------------------------
    # TODO: make it into a if-statement, what if opp didn't pick up the card?
    predecessors = [] # 2D array list of conjunctions - all possible combination of meld 
    # list of all possible SETS with opp_pick_card:
    excl_suit_list = tuple(set(SUITS).difference(opp_pick_card[1]))
    combination_list = list(combinations(excl_suit_list, 2))
    combination_list.append(excl_suit_list) # add possible set of 4 with opp_pick_card
    # print('all combination of sets with card', opp_pick_card,':', combination_list)
    for comb in combination_list:
        temp_list = []
        for each_suit in comb:
            temp_list.append(Opponent(opp_pick_card[0], each_suit))
        predecessors.append(And(temp_list))
    # list of all possible RUNS with opp_pick_card:
    temp_list = [opp_pick_card[0]]
    opp_c_list = []
    for upper_r in range(opp_pick_card[0]+1, RANKS[-1]+1):
        temp_list.append(upper_r)
        for x in list(temp_list):
            opp_c_list.append(Opponent(x, opp_pick_card[1]))
        predecessors.append(And(list(opp_c_list))) # a copy of the current list with opp card objects
    temp_list = [opp_pick_card[0]]
    opp_c_list = []
    for lower_r in reversed(range(RANKS[0], opp_pick_card[0])):
        temp_list.insert(0, lower_r)
        for x in list(temp_list):
            opp_c_list.append(Opponent(x, opp_pick_card[1]))
        predecessors.append(And(list(opp_c_list))) # a copy of the current list with opp card objects
    E.add_constraint(Opp_pick(opp_pick_card[0], opp_pick_card[1])>> Or(predecessors)) # FIXME: Find a way to print it out and verify the AND and OR is correct
   
    #-------------------------------------------------------------------------------------------------------
    # CONSTRAINT: If the opponent discards a card of “a” rank and “b” suit, the opponent does not have any meld related to that card. 
    #-------------------------------------------------------------------------------------------------------
    # FIXME: Observation: opp_pick and opp_discard have similar structure of antecedent and consequent, is there a way to simplify it??
    predecessors = [] # 2D array list of conjunctions - all possible combination of meld 
    # list of all possible SETS with opp_pick_card:
    excl_suit_list = tuple(set(SUITS).difference(opp_pick_card[1]))
    combination_list = list(combinations(excl_suit_list, 2))
    combination_list.append(excl_suit_list) # add possible set of 4 with opp_pick_card
    # print('all combination of sets with card', opp_pick_card,':', combination_list)
    for comb in combination_list:
        temp_list = []
        for each_suit in comb:
            temp_list.append(~Opponent(opp_pick_card[0], each_suit))
        predecessors.append(And(temp_list))
    # list of all possible RUNS with opp_pick_card:
    temp_list = [opp_pick_card[0]]
    opp_c_list = []
    for upper_r in range(opp_pick_card[0]+1, RANKS[-1]+1):
        temp_list.append(upper_r)
        for x in list(temp_list):
            opp_c_list.append(~Opponent(x, opp_pick_card[1]))
        predecessors.append(And(list(opp_c_list))) # a copy of the current list with opp card objects
    temp_list = [opp_pick_card[0]]
    opp_c_list = []
    for lower_r in reversed(range(RANKS[0], opp_pick_card[0])):
        temp_list.insert(0, lower_r)
        for x in list(temp_list):
            opp_c_list.append(~Opponent(x, opp_pick_card[1]))
        predecessors.append(And(list(opp_c_list))) # a copy of the current list with opp card objects
    E.add_constraint(Opp_discard(opp_pick_card[0], opp_pick_card[1])>> Or(predecessors)) 

    #-------------------------------------------------------------------------------------------------------
    # CONSTRAINT: 
    #-------------------------------------------------------------------------------------------------------

    # You can also add more customized "fancy" constraints. Use case: you don't want to enforce "exactly one"
    # for every instance of BasicPropositions, but you want to enforce it for a, b, and c.:
    # constraint.add_exactly_one(E, a, b, c)

    return E

def print_solution(sol):
    global deck
    opp_possible_card = []
    for card in deck:
        if Opponent(card[0], card[1]) in sol:
            if sol[Opponent(card[0], card[1])]:
                opp_possible_card.append(card)
    print('opponent potentially holding cards: ', opp_possible_card)
    return

if __name__ == "__main__":
    # my_list = [(1, 'A'), (2, 'A'), (2, 'B'), (3, 'A'), (7, 'A'), (8, 'A'), (8, 'B'), (8, 'C'), (8, 'D'), (9, 'A')]
    # discard_list_generator(my_list, None)
    T = example_theory()
    # Don't compile until you're finished adding all your constraints!
    T = T.compile()
    # After compilation (and only after), you can check some of the properties
    # of your model:
    print("\nSatisfiable: %s" % T.satisfiable())
    print("# Solutions: %d" % count_solutions(T))
    print("   Solution: %s" % T.solve())
    print_solution(T.solve())
    # print("\nVariable likelihoods:")
    # for v,vn in zip([a,b,c,x,y,z], 'abcxyz'):
    #     # Ensure that you only send these functions NNF formulas
    #     # Literals are compiled to NNF here
    #     print(" %s: %.2f" % (vn, likelihood(T, v)))
    print()
