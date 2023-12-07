from typing import Any
from bauhaus import Encoding, proposition, constraint, Or, And
from bauhaus.utils import count_solutions, likelihood
from itertools import product, combinations
import random
# These two lines make sure a faster SAT solver is used.
from nnf import config
config.sat_backend = "kissat"

#----------------Constants----------------- # feel free to change the size of the deck and see what the model suggests
RANKS = (1,2,3,4,5,6,7,8,9) 
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

@proposition(E)
class Deck(Hashable):
    def __init__(self, rank: int, suit: str):
        self.a = rank
        self.b = suit
    
    def __str__(self):
        return f"deck_card{self.a}{self.b}"

@proposition(E)
class Dump(Hashable):
    def __init__(self, rank: int, suit: str):
        self.a = rank
        self.b = suit
    
    def __str__(self):
        return f"dump_card{self.a}{self.b}"
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
                        potential_meld_list.append((temp_list[index-1], el_suit))
                        potential_meld_list.append((temp_list[index], el_suit))
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
            for el_suit in el_suit_set:
                potential_meld_list.append((el_rank, el_suit))
            for diff_s in temp_diff_suit:
                wanting_list.append((el_rank, diff_s))
    wanting_list = list(set(wanting_list))
    potential_meld_list = list(set(potential_meld_list))
    remaining_cards = list(set(remaining_cards).difference(potential_meld_list)) # remaining card = all cards - melds - potential melds
    return existing_meld_list, remaining_cards, wanting_list, potential_meld_list

def example_theory(player_cards, opp_pickup_list, opp_not_pickup_list, opp_discard_list):
    global deck, discarded_pile
    opp_not_want_list = []
    #-------------------------------------------------------------------------------------------------------
    # CONSTRAINT: Card(a,b) is either in the player's hand, the opponent's hand, the deck, or in the dump. 
    #             If card(a,b) is in the deck, then the player want it
    #             If card(a,b) is in the dump, or in the opponent's hand, or in the player's hand, then the player does not want it
    #-------------------------------------------------------------------------------------------------------
    for card in deck:
        constraint.add_exactly_one(E, Player(card[0], card[1]), Opponent(card[0], card[1]), Deck(card[0], card[1]), Dump(card[0], card[1]))
        E.add_constraint(Deck(card[0],card[1])>> Pl_want(card[0], card[1]))
        E.add_constraint((Dump(card[0], card[1]) | Opponent(card[0],card[1]) | Player(card[0],card[1]) ) >> ~Pl_want(card[0], card[1]))
    #-------------------------------------------------------------------------------------------------------
    # CONSTRAINT: If the card is in player card list, then the player must have that card
    #-------------------------------------------------------------------------------------------------------
    for card in player_cards:
        E.add_constraint(Player(card[0], card[1]))
    #-------------------------------------------------------------------------------------------------------
    # CONSTRAINT: Definition of a SET in player_cards
    #             Definition of a RUN in player_cards
    #-------------------------------------------------------------------------------------------------------
    pl_info_list = meld_list_generator(list(player_cards))
    for meld in pl_info_list[0]: # [('A', [3, 4, 5]), (8, {'A', 'C', 'B', 'D'})]
        if meld[0] in RANKS: # the meld is a set
            excl_suit_list = list(set(SUITS).difference(meld[1]))
            excl_suit = 'Z'
            if len(excl_suit_list)>0:
                excl_suit = excl_suit_list[0]
            E.add_constraint(Pl_set(meld[0], excl_suit))
        elif meld[0] in SUITS: # the meld is a run
            from_index = meld[1][0]
            to_index = meld[1][-1]
            E.add_constraint(Pl_run(from_index, to_index, meld[0]))
    #-------------------------------------------------------------------------------------------------------
    # CONSTRAINT: If opponent picks a card of “a” rank and “b” suit, then opponent has that card
    #             If the opponent picks a card of “a” rank and “b” suit, that card must create a meld or contribute to an existing meld.
    #-------------------------------------------------------------------------------------------------------
    for opp_pick_card in opp_pickup_list:
        E.add_constraint(Opp_pick(opp_pick_card[0], opp_pick_card[1]))
        E.add_constraint(Opp_pick(opp_pick_card[0], opp_pick_card[1]) >> Opponent(opp_pick_card[0], opp_pick_card[1]))
        predecessors = Opponent(opp_pick_card[0], opp_pick_card[1]).related_cards()
        E.add_constraint(Opp_pick(opp_pick_card[0], opp_pick_card[1])>> Or(predecessors))
    for opp_not_pick in opp_not_pickup_list:
        E.add_constraint(~Opp_pick(opp_not_pick[0], opp_not_pick[0]))
        E.add_constraint(~Opp_pick(opp_not_pick[0], opp_not_pick[0]) >> ~(Opponent(opp_not_pick[0], opp_not_pick[1])))
        E.add_constraint(~Opp_pick(opp_not_pick[0], opp_not_pick[0]) >> Dump(opp_not_pick[0], opp_not_pick[1]))
        opp_not_want_list.append(opp_not_pick)
    #-------------------------------------------------------------------------------------------------------
    # CONSTRAINT: If the opponent discards a card of “a” rank and “b” suit, the opponent does not have any meld related to that card. 
    #-------------------------------------------------------------------------------------------------------
    for opp_discard_card in opp_discard_list:
        E.add_constraint(Opp_discard(opp_discard_card[0], opp_discard_card[1])) 
        E.add_constraint(Opp_discard(opp_discard_card[0], opp_discard_card[1]) >> ~Opponent(opp_discard_card[0], opp_discard_card[1]))
        opp_not_want_list.append(opp_discard_card)
    #-------------------------------------------------------------------------------------------------------
    # CONSTRAINT: If the opponent does not want card (a,b), i.e., opponent does not pick or discard it, then they do not have related card that makes card (a,b) into a meld
    #-------------------------------------------------------------------------------------------------------
    for card in opp_not_want_list: 
        predecessors = [] # 2D array list of conjunctions - all possible combination of meld 
        # list of all possible SETS with opp_pick_card:
        excl_suit_list = list(set(SUITS).difference(card[1]))
        combination_list = list(combinations(excl_suit_list, 2))
        combination_list.append(excl_suit_list) # add possible set of 4 with opp_pick_card
        for comb in combination_list:
            temp_list = []
            for each_suit in comb:
                temp_list.append(Opponent(card[0], each_suit))
            predecessors.append(Or(temp_list))
        # list of all possible RUNS with opp_pick_card:
        temp_list = [card[0]]
        opp_c_list = []
        for upper_r in range(card[0]+1, RANKS[-1]+1):
            temp_list.append(upper_r)
            for x in list(temp_list):
                opp_c_list.append(Opponent(x, card[1]))
            predecessors.append(~And(list(opp_c_list))) # a copy of the current list with opp card objects
        temp_list = [card[0]]
        opp_c_list = []
        for lower_r in reversed(range(RANKS[0], card[0])):
            temp_list.insert(0, lower_r)
            for x in list(temp_list):
                opp_c_list.append(Opponent(x, card[1]))
            predecessors.append(~(And(list(opp_c_list)))) # a copy of the current list with opp card objects
        E.add_constraint(Opp_discard(card[0], card[1]) >> Or(predecessors))
        E.add_constraint(~Opp_pick(card[0], card[1]) >> Or(predecessors))    
    #-------------------------------------------------------------------------------------------------------
    # CONSTRAINT: If the opponent has card(a,b), we assume they will not discard it, so the player does not want that card
    #-------------------------------------------------------------------------------------------------------
    pl_info_list = meld_list_generator(list(player_cards))
    pl_wanting_list = pl_info_list[2]
    for wanting_c in pl_wanting_list:
        E.add_constraint(Pl_want(wanting_c[0], wanting_c[1]))
        E.add_constraint(Opponent(wanting_c[0], wanting_c[1]) >> ~ Pl_want(wanting_c[0], wanting_c[1]))
    return E

def initial_game() -> None :
    global deck
    deck = list (product (RANKS, SUITS))
    random.shuffle(deck)
    player_cards = deck[:NUM_OF_CARDS] # distribute cards to the player and opponent
    opponent_cards = deck[NUM_OF_CARDS:NUM_OF_CARDS*2]
    return player_cards, opponent_cards 

def one_round_of_game_opp_pl(deck_index, discard_pile_top_card, player_cards, opponent_cards):
    global deck, discarded_pile
    description_str = ''
    if deck_index >= len(deck):
        print("Deck is empty")
        return -1
    current_card = deck[deck_index]
    opp_info_list = meld_list_generator(list(opponent_cards))
    pl_info_list = meld_list_generator(list(player_cards))
    opp_pickup = False
    opp_discard = None

    if len(opp_info_list[1]) == 0 and len(opp_info_list[3]) == 0:
        print("Opponent wins!")
        return -1
    if len(pl_info_list[1]) == 0 and len(pl_info_list[3]) == 0:
        print("Player wins!")
        return -1
    
    description_str = description_str + str(discard_pile_top_card) + "      " # card facing up
    # PLAYER"S TURN
    # -------------- Step 1: Player takes a card either from the discarding pile or draw a new card -------------- 
    if discard_pile_top_card in pl_info_list[2]: # pl_info_list[2] = wanting_list
        player_cards.append(discard_pile_top_card)
        description_str = description_str + "Player picks up "+ str(discard_pile_top_card)
    # Player does not pick up and decide to draw a new card
    else:
        player_cards.append(deck[deck_index])
        discarded_pile.append(discard_pile_top_card)
        deck_index = deck_index +1
        description_str = description_str + "Player draws a card"
    if len(pl_info_list[1])>0: # pl_info_list[1] = remaining cards
        discard_pile_top_card = pl_info_list[1][-1]
    else:
        discard_pile_top_card = pl_info_list[3][-1] # pl_info_list[3] = potential_melds
    player_cards.remove(discard_pile_top_card)
    description_str = description_str + " and discard " + str(discard_pile_top_card)+ ". "
    # OPPONENT'S TURN
    # -------------- Step 2: opponent takes a card either from the discarding pile or draw a new card -------------- 
    if discard_pile_top_card in opp_info_list[2]: # if the card is in the opponent wanting list 
        opp_pickup = (True, discard_pile_top_card)        
        opponent_cards.append(discard_pile_top_card)
        description_str = description_str + "Opponent picks up " + str(discard_pile_top_card)

    else: # Opponent does not pick up and decide to draw a new card
        opp_pickup = (False, discard_pile_top_card)
        discarded_pile.append(discard_pile_top_card)
        if deck_index >= len(deck):
            print("Deck is empty")
            return -1
        opponent_cards.append(deck[deck_index])
        deck_index = deck_index +1
        description_str = description_str + "Opponent draws a card"

    # -------------- Step 3: Opponent discard a card-------------- 
    if len(opp_info_list[1])>0: # pl_info_list[1] = remaining cards
        opp_discard = opp_info_list[1][-1]
    else:
        opp_discard = opp_info_list[3][-1] # pl_info_list[3] = potential_melds
    opponent_cards.remove(opp_discard)
    discard_pile_top_card = opp_discard
    description_str = description_str + " and discard " + str(discard_pile_top_card) + "."
    return deck_index, player_cards, opponent_cards, opp_pickup, opp_discard, description_str

def print_sol_opp_holding(sol):
    global deck
    opp_possible_cards = []
    player_want_cards = []
    for card in deck:
        if sol != None and Opponent(card[0], card[1]) in sol and sol[Opponent(card[0], card[1])]:
            opp_possible_cards.append((card[0], card[1]))
        elif sol != None and Pl_want(card[0], card[1]) in sol and sol[Pl_want(card[0], card[1])]:
            player_want_cards.append((card[0], card[1]))
    return opp_possible_cards

def count_pl_meld(sol):
    pl_meld_num = 0
    if sol != None:
        for value in dict(sol):
            if sol != None and sol[value] == True:
                temp_str = str(value)
                if temp_str.__contains__("player_set") or temp_str.__contains__("player_run"):
                    pl_meld_num = pl_meld_num + 1
    return pl_meld_num

def suggest_player_want_list(sol):
    pl_wants= []
    if sol != None:
        for value in dict(sol):
            if sol != None and sol[value] == True:
                temp_str = str(value)
                if temp_str.__contains__("player_want"):
                    # print((temp_str[12:-1], temp_str[-1])) 
                    # print(temp_str + "\n")
                    pl_wants.append((temp_str[12:-1], temp_str[-1]))
    return pl_wants
if __name__ == "__main__":
    TOTAL_ROUNDS = 3
    print("|-------- Exploration 1: Play the game", TOTAL_ROUNDS,"rounds and find the cards that the opponent is potentially holding --------|\n")
    # ================= Exploration 1: Given the game runs for a few turns, guess the cards that the opponent is holding =================
    initial_info = initial_game()
    deck_index = NUM_OF_CARDS*2
    discard_pile_top_card = deck[deck_index]
    deck_index = deck_index + 1
    player_cards = initial_info[0]
    opponent_cards = initial_info[1]
    opp_pickup_list = []
    opp_not_pickup_list = []
    opp_discard_list = []
    discarded_card_list = []
    for round in range(TOTAL_ROUNDS):
        updated_game_status = one_round_of_game_opp_pl(deck_index, discard_pile_top_card, player_cards, opponent_cards) # returns a list
        if updated_game_status != -1:
            print("Round", round+1, updated_game_status[5])

        if updated_game_status == -1:
            print("Game over!\n")
            print("Player cards: ", sorted(player_cards))
            print("Opponent cards: ", sorted(opponent_cards))
            exit()
        else: 
            deck_index = updated_game_status[0]
            player_cards = updated_game_status[1]
            opponent_cards = updated_game_status[2]
            if (updated_game_status[3][0]): # if opponent picked up
                opp_pickup_list.append(updated_game_status[3][1])
            else: # if opponent does not pick up
                opp_not_pickup_list.append(updated_game_status[3][1])
            opp_discard_list.append(updated_game_status[4])
            discard_pile_top_card = updated_game_status[4]

    T1 = example_theory(player_cards, opp_pickup_list, opp_not_pickup_list, opp_discard_list)
    T1 = T1.compile()
    solution = T1.solve()
    satisfiable = T1.satisfiable()
    print("\nPlayer cards:", sorted(player_cards))
    print("Opponent cards:", sorted(opponent_cards), "\n")

    print("\n----------------- Exploration 1 OUTPUT: -----------------\n")

    if satisfiable == False:
        print("The model is not satisfiable.")
    else: 
       
        opp_guess = print_sol_opp_holding(solution)
        accuarcy = 0
        for opp_c in opp_guess:
            if opp_c in opponent_cards:
                accuarcy = accuarcy + 1
        print('The opponent is potentially holding cards: ', sorted(opp_guess))
        print(f'{accuarcy}/{len(opp_guess)} guess of the opponent cards are correct.')

    # ================= Exploration 2: Given this facing up card, how should the player make the best move? =================
    print("\n\n|------------- Exploration 2: Given a state of the game, determine whether the player's best next step -------------|\n")

    print("The card facing up is ", discard_pile_top_card)
    print("Cards have been discarded are:", sorted(discarded_pile))
    print("Player cards:", sorted(player_cards), "\n")

    # T_NP is the model if player does not pick up
    discarded_pile.append(discard_pile_top_card)
    T_NP = example_theory(player_cards, opp_pickup_list, opp_not_pickup_list, opp_discard_list)
    T_NP = T_NP.compile()
    n_pick_up_sol = count_solutions(T_NP)
    np_meld = count_pl_meld(T_NP.solve())

    # T_P is the model if the player picks up the card
    discarded_pile.remove(discard_pile_top_card)
    player_cards.append(discard_pile_top_card)
    T_P = example_theory(player_cards, opp_pickup_list, opp_not_pickup_list, opp_discard_list)
    T_P = T_P.compile()
    pick_up_sol = count_solutions(T_P)
    p_meld = count_pl_meld(T_P.solve())

    pl_wants = suggest_player_want_list(T_P.solve())
    
    print("\n----------------- Exploration 2 OUTPUT: -----------------\n")

    if not T_P.satisfiable() and not T_NP.satisfiable():
        print("The model is not satisfiable.")
    else:
        if pick_up_sol-n_pick_up_sol > 0 or p_meld - np_meld > 0: # there exist more model if the player picks up the discarding card.  
            print("The model suggests the player to pick up the card", discard_pile_top_card, "from the discarding pile. ") 
        elif pick_up_sol == n_pick_up_sol: # there is no difference in the number of solution that satisfy the model if the player picks up or not
            print("the number of solutions is the same either the player picks up the card or not.")
        else: # there exist more model if the player does NOT pick up the discarding card, i.e. should draw a new card from the deck, OR there is solution that satisfy the model
            print("The model suggests the player to NOT pick up the card", discard_pile_top_card, "and draws a new card from the deck. ") 
    
    if len(pl_wants)<1:
        print("\nThere is no card that is still in the deck for player to win, consider rearranging your melds.")
    else:
        print("\nThe model sugguest the cards that is still possible to pick up from the player and would lead to a win are:\n", sorted(pl_wants))
    print()

