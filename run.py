
from bauhaus import Encoding, proposition, constraint
from bauhaus.utils import count_solutions, likelihood
from itertools import product
import random
# These two lines make sure a faster SAT solver is used.
from nnf import config
config.sat_backend = "kissat"

#----------------Constants-----------------
RANKS = (1,2,3,4,5,6,7,8,9) # tuple: ordered and unchangable data structure
SUITS = ('A', 'B', 'C', 'D')
NUM_OF_CARDS = 10
#-------------Global Variables-------------
deck = []
discard = []
player_cards = []

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
    def __init__(self, a, b): # a = rank, b = suit
        self.a = a
        self.b = b

    def __str__(self):
        return f"P({self.a}{self.b})"
    
@proposition(E)
class Opponent(Hashable):
    def __init__(self, a, b): # a = rank, b = suit
        self.a = a
        self.b = b

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
    def __init__(self, related_cards):
        self.related_set_cards = related_cards

    def __str__(self):
        return f"player_set_[{self.related_set_cards}]"
    
@proposition(E)
class Want(Hashable):
    def __init__(self, a, b):
        self.a = a
        self.b = b

    def __str__(self):
        return f"player_want({self.a}{self.b})"

def cardlist_to_dict(my_cardlist):
    my_dict = {} # dictionary that maps the ranks into a set of suits, eg. {1:{'A', 'B'}, 3:{'C','A'}}
    for x in my_cardlist:
        if x[0] in my_dict:
            my_dict[x[0]].add(x[1])
        else:
            my_dict[x[0]] = {x[1]}
    print("after", my_dict)
    return my_dict

def initial_game():
    # reset the two global variable and create a shuffled deck
    deck = []
    discard = []
    deck = list (product (RANKS, SUITS))
    random.shuffle(deck)
    # distribute cards to the player and opponent
    player_cards = deck[:NUM_OF_CARDS]
    # opponent = Player('Opponent', deck[NUM_OF_CARDS:NUM_OF_CARDS*2])
    # deck = deck[NUM_OF_CARDS*2:]
    # print("deck:", deck)
    # print(player_cards)
    # print(opponent)
    return player_cards



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
    player_cards = initial_game()

    # Add custom constraints by creating formulas with the variables you created. 
    print("player cards: ", player_cards)
    # CCONSTRAINT: If player has card(a,b), then Opponent does not have card(a,b)
    for card in player_cards:
        E.add_constraint(Player(card[0], card[1]) >> ~Opponent(card[0], card[1]))
        
    #CONSTRAINT: check in player_cards for SETS
    pl_cards_dict = cardlist_to_dict(sorted(player_cards))
    for el_set in pl_cards_dict.items():
        if (len(el_set[1])>2):
            print("there exist a set", el_set)
            # E.add_constraint(Pl_run)

    #CONSTRAINT: check in player_cards for RUNS
    is_consecutive = all(pl_cards_dict[i] == pl_cards_dict[i-1] + 1 for i in range(1, len(pl_cards_dict)))
    print(is_consecutive)


    #CONSTRAINT: If player does not have the card and opponent have no 


    # You can also add more customized "fancy" constraints. Use case: you don't want to enforce "exactly one"
    # for every instance of BasicPropositions, but you want to enforce it for a, b, and c.:
    # constraint.add_exactly_one(E, a, b, c)

    return E


if __name__ == "__main__":
    T = example_theory()
    # Don't compile until you're finished adding all your constraints!
    T = T.compile()
    # After compilation (and only after), you can check some of the properties
    # of your model:
    print("\nSatisfiable: %s" % T.satisfiable())
    print("# Solutions: %d" % count_solutions(T))
    print("   Solution: %s" % T.solve())

    # print("\nVariable likelihoods:")
    # for v,vn in zip([a,b,c,x,y,z], 'abcxyz'):
    #     # Ensure that you only send these functions NNF formulas
    #     # Literals are compiled to NNF here
    #     print(" %s: %.2f" % (vn, likelihood(T, v)))
    print()
