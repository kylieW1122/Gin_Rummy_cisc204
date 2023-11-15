
from typing import Any
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
global deck, discarded_pile
discarded_pile = []

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
        self.rank = rank
        self.suit = suit
    
    def related_cards(self) -> list:
        related_list = [] # 2D array list of conjunctions - all possible combination of meld 
        # list of all possible SETS with opp_pick_card:
        excl_suit_list = list(set(SUITS).difference(self.suit))
        combination_list = list(combinations(excl_suit_list, 2))
        combination_list.append(excl_suit_list) # add possible set of 4 with opp_pick_card
        # print('all combination of sets with card', opp_pick_card,':', combination_list)
        for comb in combination_list:
            temp_list = []
            for each_suit in comb:
                temp_list.append(Opponent(self.rank, each_suit))
            related_list.append(And(temp_list))
        # list of all possible RUNS with opp_pick_card:
        temp_list = [self.rank]
        opp_c_list = []
        for upper_r in range(self.rank, RANKS[-1]+1):
            temp_list.append(upper_r)
            for x in list(temp_list):
                opp_c_list.append(Opponent(x, self.suit))
            related_list.append(And(list(opp_c_list))) # a copy of the current list with opp card objects
        temp_list = [self.rank]
        opp_c_list = []
        for lower_r in reversed(range(RANKS[0], self.rank)):
            temp_list.insert(0, lower_r)
            for x in list(temp_list):
                opp_c_list.append(Opponent(x, self.suit))
            related_list.append(And(list(opp_c_list))) # a copy of the current list with opp card objects
            # print(related_list) # FIXME: Find a way to print it out and verify the AND and OR is correct
        return related_list
    def __str__(self):
        return f"O({self.rank}{self.suit})"
    
@proposition(E)
class Pl_run(Hashable):
    def __init__(self, lower_rank, upper_rank, suit):
        self.lower = lower_rank
        self.upper = upper_rank
        self.suit = suit

    def __str__(self):
        return f"player_run_{self.lower}_{self.upper}_{self.suit}"

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
def sort_tuple_card_list(card_list: list) -> list:
    sorted_list = []
    temp_dict = cards_to_rank_dict(sorted(card_list))
    for rank, suit_set in temp_dict.items():
        for suit in suit_set:
            sorted_list.append((rank, suit))
    return sorted_list

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

def remove_card_from_list(cards: list, remove_items, rank: int, suit: str) -> list:
    if rank == None:
        for target in remove_items:
            cards.remove((target, suit))
    else:
        for target in remove_items:
            cards.remove((rank, target))
    return cards # updated card list that removes the target items
# def add_to_wanting()
def meld_list_generator(remaining_cards:list) -> list:
    '''
    Takes in a list of cards, find all the existing melds and potential melds
    Return a list of three lists: [existing_meld_list, remaining_cards, potential_meld_list]
    '''
    existing_meld_list = []
    potential_meld_list = []
    wanting_list = []
    # search for RUNS
    cards_in_suit = cards_to_suit_dict(sorted(remaining_cards))
    for el_suit, el_rank_set in cards_in_suit.items():
        if(len(el_rank_set)>2):
            temp_list = sorted(list(el_rank_set))
            num_of_con_term = 1
            from_index = 0
            # Search for existing RUNS
            for index in range (len(temp_list)):
                if index == len(temp_list)-1: # check if the last element counts towards a run
                    if (((temp_list[index-1]+1) == temp_list[index]) and (num_of_con_term>2)):
                        existing_meld_list.append((el_suit,temp_list[from_index:index+1]))        
                        wanting_list.append((temp_list[from_index]-1, el_suit))
                        remaining_cards = remove_card_from_list(remaining_cards, temp_list[from_index:index+1], None, el_suit)
                elif ((temp_list[index]+1) != temp_list[index+1]): # if the index card is not consecative with the next card
                    # if the previous cards makes a run, add them into the existing_meld
                    if num_of_con_term >2: 
                        existing_meld_list.append((el_suit,temp_list[from_index:index+1]))
                        if temp_list[from_index] > RANKS[0]:
                            wanting_list.append((temp_list[from_index]-1, el_suit))
                        if temp_list[index]+1 < RANKS[-1]:
                            wanting_list.append((temp_list[index]+1, el_suit))
                        remaining_cards = remove_card_from_list(remaining_cards, temp_list[from_index:index+1], None, el_suit)
                        from_index = index + 1
                    # if there is a potential meld, with Case 1: input_card = [4A, 5A] => wanting_list = [3A, 6A]
                    elif num_of_con_term == 2: 
                        # potential_meld_list.append((temp_list[index-1], el_suit))
                        # potential_meld_list.append((temp_list[index], el_suit))
                        # remaining_cards = remove_card_from_list(remaining_cards, temp_list[index-1:index+1], None, el_suit)
                        if temp_list[index-1] > RANKS[0]:
                            wanting_list.append((temp_list[index-1]-1, el_suit))
                        if temp_list[index]+1 < RANKS[-1]:
                            wanting_list.append((temp_list[index]+1, el_suit))
                    num_of_con_term = 1
                    from_index = index +1
                # if the two cards are consecutive
                elif ((temp_list[index]+1) == temp_list[index+1]): 
                    num_of_con_term +=1 
                # potential meld with Case 2: input_card = [4A, 6A], wanting_list = [5A]
                elif (index<len(temp_list)-2) and ((temp_list[index]+2) == temp_list[index+2]): 
                    if temp_list[index-1] > RANKS[0]:
                        wanting_list.append((temp_list[index-1]-1, el_suit))
                    if temp_list[index]+1 < RANKS[-1]:
                        wanting_list.append((temp_list[index]+1, el_suit))
    # search for SETS
    cards_in_rank = cards_to_rank_dict(sorted(remaining_cards))
    for el_rank, el_suit_set in cards_in_rank.items():
        if (len(el_suit_set)>2):
            existing_meld_list.append((el_rank, el_suit_set))
            remaining_cards = remove_card_from_list(remaining_cards, list(el_suit_set), el_rank, None)
        elif (len(el_suit_set)==2): # potential sets, add related cards to wanting linst
            temp_diff_suit = list(set(SUITS).difference(el_suit_set))
            for diff_s in temp_diff_suit:
                wanting_list.append((el_rank, diff_s))
    wanting_list = list(set(wanting_list))
    # print('existing melds:', existing_meld_list)
    # print('remaining cards:', sorted(remaining_cards))
    # print('wanting:', sorted(wanting_list))
    return existing_meld_list, remaining_cards, wanting_list

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
def example_theory(player_cards, opp_pickup_list, opp_not_pickup_list, opp_discard_list):
    # INITIALIZE VARIABLES for the game
    global deck
    opp_not_list = []
    # print("input to example theory:", player_cards, opp_pickup_list, opp_not_pickup_list, opp_discard_list)
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
    pl_cards_dict = cards_to_rank_dict(sorted(player_cards)) # pl_card_dict = {1:{'A','B'}, ....}
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
    cards_in_suit = cards_to_suit_dict(sorted(player_cards))
    for el_suit, el_rank_set in cards_in_suit.items():
        if(len(el_rank_set)>2):
            temp_list = sorted(list(el_rank_set))
            num_of_con_term = 1
            from_index = 0
            # Search for existing RUNS
            for index in range (len(temp_list)):
                if index == len(temp_list)-1: # check if the last element counts towards a run
                    if (((temp_list[index-1]+1) == temp_list[index]) and (num_of_con_term>2)):
                        E.add_constraint(Pl_run(temp_list[from_index], temp_list[index], el_suit))
                elif ((temp_list[index]+1) != temp_list[index+1]): # if the two cards are NOT consecutive
                    if num_of_con_term >2: # if the previous cards makes a run, add them into the existing_meld
                        # existing_meld_list.append((el_suit,temp_list[from_index:index+1]))
                        E.add_constraint(Pl_run(temp_list[from_index], temp_list[index], el_suit))
                        from_index = index + 1
                    num_of_con_term = 1
                    from_index = index +1
                elif ((temp_list[index]+1) == temp_list[index+1]): # if the two cards are consecutive
                    num_of_con_term +=1 
    
    #-------------------------------------------------------------------------------------------------------
    # CONSTRAINT: If opponent picks a card of “a” rank and “b” suit, then opponent has that card
    #             If the opponent picks a card of “a” rank and “b” suit, that card must create a meld or contribute to an existing meld.
    #-------------------------------------------------------------------------------------------------------
    for opp_pick_card in opp_pickup_list:
        temp_opp_card = Opponent(opp_pick_card[0], opp_pick_card[1])
        E.add_constraint(Opp_pick(opp_pick_card[0], opp_pick_card[1]))
        E.add_constraint(Opp_pick(opp_pick_card[0], opp_pick_card[1]) >> Opponent(opp_pick_card[0], opp_pick_card[1]))
        predecessors = temp_opp_card.related_cards()
        E.add_constraint(Opp_pick(opp_pick_card[0], opp_pick_card[1])>> Or(predecessors)) # FIXME: Find a way to print it out and verify the AND and OR is correct
    for opp_not_pick in opp_not_pickup_list:
        E.add_constraint(~Opp_pick(opp_not_pick[0], opp_not_pick[0]))
        E.add_constraint(~Opp_pick(opp_not_pick[0], opp_not_pick[0]) >> ~Opponent(opp_not_pick[0], opp_not_pick[1]))
    #-------------------------------------------------------------------------------------------------------
    # CONSTRAINT: If the opponent discards a card of “a” rank and “b” suit, the opponent does not have any meld related to that card. 
    #-------------------------------------------------------------------------------------------------------
    # Opponent: randomly pick a card to discard from the cards that does not make a meld
    for opp_discard_card in opp_discard_list:
        E.add_constraint(Opp_discard(opp_discard_card[0], opp_discard_card[1])) 
        E.add_constraint(Opp_discard(opp_discard_card[0], opp_discard_card[1]) >> ~Opponent(opp_discard_card[0], opp_discard_card[1]))
        opp_not_list.append(opp_discard_card)

    #-------------------------------------------------------------------------------------------------------
    # CONSTRAINT: If the opponent does not want card (a,b), i.e., opponent does not pick or discard it, then they do not have related card that makes card (a,b) into a meld
    #-------------------------------------------------------------------------------------------------------
    for card in opp_not_list:
        predecessors = [] # 2D array list of conjunctions - all possible combination of meld 
        # list of all possible SETS with opp_pick_card:
        excl_suit_list = list(set(SUITS).difference(card[1]))
        combination_list = list(combinations(excl_suit_list, 2))
        combination_list.append(excl_suit_list) # add possible set of 4 with opp_pick_card
        for comb in combination_list:
            temp_list = []
            for each_suit in comb:
                temp_list.append(Opponent(card[0], each_suit))
            predecessors.append(And(temp_list))
        # list of all possible RUNS with opp_pick_card:
        temp_list = [card[0]]
        opp_c_list = []
        for upper_r in range(card[0]+1, RANKS[-1]+1):
            temp_list.append(upper_r)
            for x in list(temp_list):
                opp_c_list.append(Opponent(x, card[1]))
            predecessors.append(And(list(opp_c_list))) # a copy of the current list with opp card objects
        temp_list = [card[0]]
        opp_c_list = []
        for lower_r in reversed(range(RANKS[0], card[0])):
            temp_list.insert(0, lower_r)
            for x in list(temp_list):
                opp_c_list.append(Opponent(x, card[1]))
            predecessors.append(~And(list(opp_c_list))) # a copy of the current list with opp card objects
        E.add_constraint((~Opp_discard(card[0], card[1]) | ~Opp_pick(card[0], card[1])) >> Or(predecessors))    
    #-------------------------------------------------------------------------------------------------------
    # CONSTRAINT: If a card is in the discarding pile, both the player and the opponent does not have the card
    #-------------------------------------------------------------------------------------------------------
    for discarded_card in discarded_pile:
        E.add_constraint(~Player(discarded_card[0], discarded_card[1]) & ~Opponent(discarded_card[0], discarded_card[1]))
    # You can also add more customized "fancy" constraints. Use case: you don't want to enforce "exactly one"
    # for every instance of BasicPropositions, but you want to enforce it for a, b, and c.:
    # constraint.add_exactly_one(E, a, b, c)
    
    # print('player cards: ', sorted(player_cards)) 
    # print('opponent cards after pick or not pick:', sorted(opponent_cards)) 
    # print('opponent pick up:', opp_pickup_list)
    # print('opponent discard:', opp_discard_list)
    return E

def print_solution(sol):
    global deck
    opp_possible_card = []
    for card in deck:
        if sol != None and Opponent(card[0], card[1]) in sol and sol[Opponent(card[0], card[1])]:
            opp_possible_card.append((card[0], card[1]))
    print('opponent potentially holding cards: ', sorted(opp_possible_card))
    return

def initial_game() -> None :
    # reset the two global variable and create a shuffled deck
    global deck
    deck = list (product (RANKS, SUITS))
    random.shuffle(deck)
    # distribute cards to the player and opponent
    # player_cards =  [(1, 'C'), (1, 'D'), (2, 'B'), (3, 'B'), (4, 'A'), (4, 'C'), (5, 'A'), (7, 'B'), (8, 'C'), (9, 'D')]
    # opponent_cards = [(1, 'A'), (2, 'A'), (2, 'D'), (3, 'C'), (3, 'D'), (4, 'B'), (5, 'D'), (7, 'A'), (8, 'D'), (9, 'C')]
    player_cards = deck[:NUM_OF_CARDS]
    opponent_cards = deck[NUM_OF_CARDS:NUM_OF_CARDS*2]
    return deck, player_cards, opponent_cards 

def one_round_of_game_opp_pl(deck_index, discard_pile_top_card, player_cards, opponent_cards):
    global deck, discarded_pile
    assert deck_index < len(deck), "reached the bottom of the deck, end of game"
    current_card = deck[deck_index]
    opp_info_list = meld_list_generator(list(opponent_cards))
    pl_info_list = meld_list_generator(list(player_cards))
    opp_pickup = False
    opp_discard = None
    if len(opp_info_list[1]) == 0:
        print("Opponent wins!")
        return
    if len(pl_info_list[1]) == 0:
        print("Player wins!")
        return
    
    # print("---------------------------------------------------------------")
    # print("facing up card (pl's discard) ", discard_pile_top_card)
    # print("opponent's cards: ", sorted(opponent_cards))
    
    # OPPONENT'S TURN
    # -------------- Step 1: opponent takes a card either from the discarding pile or draw a new card -------------- 
    # Opponent picks up the card in the discarding pile, i.e. the previous player discarded card
    if discard_pile_top_card in opp_info_list[2]:
        opp_pickup = True        
        opponent_cards.append(discard_pile_top_card)
    # Opponent does not pick up and decide to draw a new card
    else:
        opp_pickup = False
        discarded_pile.append(discard_pile_top_card)
        opponent_cards.append(deck[deck_index])
        deck_index = deck_index +1
    # -------------- Step 2: Opponent discard a card-------------- 
    opp_discard = opp_info_list[1][-1]
    opponent_cards.remove(opp_info_list[1][-1])
    discard_pile_top_card = opp_discard
    # print("opponent discard: ", discard_pile_top_card)
    # print("facing up card (opp's discard) ", discard_pile_top_card)
    # print("players's cards: ", sorted(player_cards))
    # PLAYER"S TURN
    # -------------- Step 3: Player takes a card either from the discarding pile or draw a new card -------------- 
    if discard_pile_top_card in pl_info_list[2]:
        player_cards.append(discard_pile_top_card)
    # Player does not pick up and decide to draw a new card
    else:
        player_cards.append(deck[deck_index])
        discarded_pile.append(discard_pile_top_card)
        deck_index = deck_index +1
    discard_pile_top_card = pl_info_list[1][-1]
    discarded_pile.append(discard_pile_top_card)
    player_cards.remove(pl_info_list[1][-1])
    # print("player discard: ", discard_pile_top_card)
    # print("---------------------------------------------------------------")
    return deck_index, discard_pile_top_card, player_cards, opponent_cards, opp_pickup, opp_discard # opp_pickup = true/false, card he pick up == discard_pile_top_card

if __name__ == "__main__":
    # ================= Exploration 1: Given the game runs for a few turns, guess the cards that the opponent is holding =================
    initial_info = initial_game()
    # deck = initial_info[0]
    deck_index = NUM_OF_CARDS*2
    discard_pile_top_card = deck[deck_index]
    deck_index = deck_index + 1
    player_cards = initial_info[1]
    opponent_cards = initial_info[2]
    opp_pickup_list = []
    opp_not_pickup_list = []
    opp_discard_list = []
    discarded_card_list = []
    for round in range(1):
        updated_game_status = one_round_of_game_opp_pl(deck_index, discard_pile_top_card, player_cards, opponent_cards) # returns a list
        deck_index = updated_game_status[0]
        player_cards = updated_game_status[2]
        opponent_cards = updated_game_status[3]
        if (updated_game_status[4]): # if opponent picked up
            opp_pickup_list.append(discard_pile_top_card)
        else:
            opp_not_pickup_list.append(discard_pile_top_card)
        opp_discard_list.append(updated_game_status[5])
        discard_pile_top_card = updated_game_status[1]
        # print("\n-----------------AFTER-----------------------")
        # print("player:", sorted(player_cards))
        # print("opponent: ", sorted(opponent_cards))

    T = example_theory(player_cards, opp_pickup_list, opp_not_pickup_list, opp_discard_list)
    print("opponent cards:", sorted(opponent_cards))
    # Don't compile until you're finished adding all your constraints!
    T = T.compile()
    # After compilation (and only after), you can check some of the properties
    # of your model:
    print("\nSatisfiable: %s" % T.satisfiable())
    print("# Solutions: %d" % count_solutions(T))
    # print("   Solution: %s" % T.solve())
    sol = T.solve()
    # print(sol)
    print_solution(sol)
    # ================= Exploration 2: Given this facing up card, how should the player make the best move? =================
    
    # print("\nVariable likelihoods:")
    # for v,vn in zip([a,b,c,x,y,z], 'abcxyz'):
    #     # Ensure that you only send these functions NNF formulas
    #     # Literals are compiled to NNF here
    #     print(" %s: %.2f" % (vn, likelihood(T, v)))
    print()
