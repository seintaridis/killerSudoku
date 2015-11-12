"""CSP (Constraint Satisfaction Problems) problems and solvers. (Chapter 6)."""

from utils import *
import search
import time

class CSP(search.Problem):
    """This class describes finite-domain Constraint Satisfaction Problems.
    A CSP is specified by the following inputs:
        vars        A list of variables; each is atomic (e.g. int or string).
        domains     A dict of {var:[possible_value, ...]} entries.
        neighbors   A dict of {var:[var,...]} that for each variable lists
                    the other variables that participate in constraints.
        constraints A function f(A, a, B, b) that returns true if neighbors
                    A, B satisfy the constraint when they have values A=a, B=b
    In the textbook and in most mathematical definitions, the
    constraints are specified as explicit pairs of allowable values,
    but the formulation here is easier to express and more compact for
    most cases. (For example, the n-Queens problem can be represented
    in O(n) space using this notation, instead of O(N^4) for the
    explicit representation.) In terms of describing the CSP as a
    problem, that's all there is.

    However, the class also supports data structures and methods that help you
    solve CSPs by calling a search function on the CSP.  Methods and slots are
    as follows, where the argument 'a' represents an assignment, which is a
    dict of {var:val} entries:
        assign(var, val, a)     Assign a[var] = val; do other bookkeeping
        unassign(var, a)        Do del a[var], plus other bookkeeping
        nconflicts(var, val, a) Return the number of other variables that
                                conflict with var=val
        curr_domains[var]       Slot: remaining consistent values for var
                                Used by constraint propagation routines.
    The following methods are used only by graph_search and tree_search:
        actions(state)          Return a list of actions
        result(state, action)   Return a successor of state
        goal_test(state)        Return true if all constraints satisfied
    The following are just for debugging purposes:
        nassigns                Slot: tracks the number of assignments made
        display(a)              Print a human-readable representation

    >>> search.depth_first_graph_search(australia)
    <Node (('WA', 'B'), ('Q', 'B'), ('T', 'B'), ('V', 'B'), ('SA', 'G'), ('NT', 'R'), ('NSW', 'R'))>
    """

    def __init__(self, vars, domains, neighbors, constraints):
        "Construct a CSP problem. If vars is empty, it becomes domains.keys()."
        vars = vars or domains.keys()
        update(self, vars=vars, domains=domains,
               neighbors=neighbors, constraints=constraints,
               initial=(), curr_domains=None, nassigns=0)

    def assign(self, var, val, assignment):
        "Add {var: val} to assignment; Discard the old value if any."
        assignment[var] = val
        self.nassigns += 1

    def unassign(self, var, assignment):
        """Remove {var: val} from assignment.
        DO NOT call this if you are changing a variable to a new value;
        just call assign for that."""
        if var in assignment:
            del assignment[var]

    def nconflicts(self, var, val, assignment): #it's the same of that in csp.py except it has the counter of arc consistency
		def conflict(var2):
			if var2 in assignment:
				self.count = self.count + 1
			return (var2 in assignment and not self.constraints(var, val, var2, assignment[var2]))
		return count_if(conflict, self.neighbors[var])

        
    

    def display(self, assignment):
        "Show a human-readable representation of the CSP."
        # Subclasses can print in a prettier way, or display with a GUI
        print 'CSP:', self, 'with assignment:', assignment

    ## These methods are for the tree- and graph-search interface:

    def actions(self, state):
        """Return a list of applicable actions: nonconflicting
        assignments to an unassigned variable."""
        if len(state) == len(self.vars):
            return []
        else:
            assignment = dict(state)
            var = find_if(lambda v: v not in assignment, self.vars)
            return [(var, val) for val in self.domains[var]
                    if self.nconflicts(var, val, assignment) == 0]

    def result(self, state, (var, val)):
        "Perform an action and return the new state."
        return state + ((var, val),)

    def goal_test(self, state):
        "The goal is to assign all vars, with all constraints satisfied."
        assignment = dict(state)
        return (len(assignment) == len(self.vars) and
                every(lambda var: self.nconflicts(var, assignment[var],
                                                  assignment) == 0,
                      self.vars))

    ## These are for constraint propagation

    def support_pruning(self):
        """Make sure we can prune values from domains. (We want to pay
        for this only if we use it.)"""
        if self.curr_domains is None:
            self.curr_domains = dict((v, list(self.domains[v]))
                                     for v in self.vars)

    def suppose(self, var, value):
        "Start accumulating inferences from assuming var=value."
        self.support_pruning()
        removals = [(var, a) for a in self.curr_domains[var] if a != value]
        self.curr_domains[var] = [value]
        return removals

    def prune(self, var, value, removals):
        "Rule out var=value."
        self.curr_domains[var].remove(value)
        if removals is not None: removals.append((var, value))

    def choices(self, var):
        "Return all values for var that aren't currently ruled out."
        return (self.curr_domains or self.domains)[var]

    def infer_assignment(self):
        "Return the partial assignment implied by the current inferences."
        self.support_pruning()
        return dict((v, self.curr_domains[v][0])
                    for v in self.vars if 1 == len(self.curr_domains[v]))

    def restore(self, removals):
        "Undo a supposition and all inferences from it."
        for B, b in removals:
            self.curr_domains[B].append(b)

    ## This is for min_conflicts search

    def conflicted_vars(self, current):
        "Return a list of variables in current assignment that are in conflict"
        return [var for var in self.vars
                if self.nconflicts(var, current[var], current) > 0]

#______________________________________________________________________________
# Constraint Propagation with AC-3

def AC3(csp, queue=None, removals=None):
    """[Fig. 6.3]"""
    if queue is None:
        queue = [(Xi, Xk) for Xi in csp.vars for Xk in csp.neighbors[Xi]]
    csp.support_pruning()
    while queue:
        (Xi, Xj) = queue.pop()
        if revise(csp, Xi, Xj, removals):
            if not csp.curr_domains[Xi]:
                return False
            for Xk in csp.neighbors[Xi]:
                if Xk != Xi:
                    queue.append((Xk, Xi))
    return True

def revise(csp, Xi, Xj, removals):
    "Return true if we remove a value."
    revised = False
    for x in csp.curr_domains[Xi][:]:
        # If Xi=x conflicts with Xj=y for every possible y, eliminate Xi=x
        if every(lambda y: not csp.constraints(Xi, x, Xj, y),
                 csp.curr_domains[Xj]):
            csp.prune(Xi, x, removals)
            revised = True
    return revised

#______________________________________________________________________________
# CSP Backtracking Search

# Variable ordering

def first_unassigned_variable(assignment, csp):
    "The default variable order."
    return find_if(lambda var: var not in assignment, csp.vars)

def mrv(assignment, csp):
    "Minimum-remaining-values heuristic."
    return argmin_random_tie(
        [v for v in csp.vars if v not in assignment],
        lambda var: num_legal_values(csp, var, assignment))

def num_legal_values(csp, var, assignment):
    if csp.curr_domains:
        return len(csp.curr_domains[var])
    else:
        return count_if(lambda val: csp.nconflicts(var, val, assignment) == 0,
                        csp.domains[var])

# Value ordering

def unordered_domain_values(var, assignment, csp):
    "The default value order."
    return csp.choices(var)

def lcv(var, assignment, csp):
    "Least-constraining-values heuristic."
    return sorted(csp.choices(var),
                  key=lambda val: csp.nconflicts(var, val, assignment))

# Inference

def no_inference(csp, var, value, assignment, removals):
    return True

def forward_checking(csp, var, value, assignment, removals):
    "Prune neighbor values inconsistent with var=value."
    for B in csp.neighbors[var]:
        if B not in assignment:
            for b in csp.curr_domains[B][:]:
                if not csp.constraints(var, value, B, b):
                    csp.prune(B, b, removals)
            if not csp.curr_domains[B]:
                return False
    return True

def mac(csp, var, value, assignment, removals):
    "Maintain arc consistency."
    return AC3(csp, [(X, var) for X in csp.neighbors[var]], removals)

# The search, proper

def backtracking_search(csp,
                        select_unassigned_variable = first_unassigned_variable,
                        order_domain_values = unordered_domain_values,
                        inference = no_inference):
    """[Fig. 6.5]
    >>> backtracking_search(australia) is not None
    True
    >>> backtracking_search(australia, select_unassigned_variable=mrv) is not None
    True
    >>> backtracking_search(australia, order_domain_values=lcv) is not None
    True
    >>> backtracking_search(australia, select_unassigned_variable=mrv, order_domain_values=lcv) is not None
    True
    >>> backtracking_search(australia, inference=forward_checking) is not None
    True
    >>> backtracking_search(australia, inference=mac) is not None
    True
    >>> backtracking_search(usa, select_unassigned_variable=mrv, order_domain_values=lcv, inference=mac) is not None
    True
    """

    def backtrack(assignment):
        if len(assignment) == len(csp.vars):
            return assignment
        var = select_unassigned_variable(assignment, csp)
        for value in order_domain_values(var, assignment, csp):
            if 0 == csp.nconflicts(var, value, assignment):
                csp.assign(var, value, assignment)
                removals = csp.suppose(var, value)
                if inference(csp, var, value, assignment, removals):
                    result = backtrack(assignment)
                    if result is not None:
                        return result
                csp.restore(removals)
        csp.unassign(var, assignment)
        return None

    result = backtrack({})
    assert result is None or csp.goal_test(result)
    return result

#______________________________________________________________________________
# Min-conflicts hillclimbing search for CSPs

def min_conflicts(csp, max_steps=100000):
    """Solve a CSP by stochastic hillclimbing on the number of conflicts."""
    # Generate a complete assignment for all vars (probably with conflicts)
    csp.current = current = {}
    for var in csp.vars:
        val = min_conflicts_value(csp, var, current)
        csp.assign(var, val, current)
    # Now repeatedly choose a random conflicted variable and change it
    for i in range(max_steps):
        conflicted = csp.conflicted_vars(current)
        if not conflicted:
            return current
        var = random.choice(conflicted)
        val = min_conflicts_value(csp, var, current)
        csp.assign(var, val, current)
    return None

def min_conflicts_value(csp, var, current):
    """Return the value that will give var the least number of conflicts.
    If there is a tie, choose at random."""
    return argmin_random_tie(csp.domains[var],
                             lambda val: csp.nconflicts(var, val, current))

#______________________________________________________________________________

def tree_csp_solver(csp):
    "[Fig. 6.11]"
    n = len(csp.vars)
    assignment = {}
    root = csp.vars[0]
    X, parent = topological_sort(csp.vars, root)
    for Xj in reversed(X):
        if not make_arc_consistent(parent[Xj], Xj, csp):
            return None
    for Xi in X:
        if not csp.curr_domains[Xi]:
            return None
        assignment[Xi] = csp.curr_domains[Xi][0]
    return assignment

def topological_sort(xs, x):
    unimplemented()

def make_arc_consistent(Xj, Xk, csp): 
    unimplemented()

#______________________________________________________________________________
# Map-Coloring Problems

class UniversalDict:
    """A universal dict maps any key to the same value. We use it here
    as the domains dict for CSPs in which all vars have the same domain.
    >>> d = UniversalDict(42)
    >>> d['life']
    42
    """
    def __init__(self, value): self.value = value
    def __getitem__(self, key): return self.value
    def __repr__(self): return '{Any: %r}' % self.value

def different_values_constraint(A, a, B, b):
    "A constraint saying two neighboring variables must differ in value."
    return a != b

def MapColoringCSP(colors, neighbors):
    """Make a CSP for the problem of coloring a map with different colors
    for any two adjacent regions.  Arguments are a list of colors, and a
    dict of {region: [neighbor,...]} entries.  This dict may also be
    specified as a string of the form defined by parse_neighbors."""
    if isinstance(neighbors, str):
        neighbors = parse_neighbors(neighbors)
    return CSP(neighbors.keys(), UniversalDict(colors), neighbors,
               different_values_constraint)

def parse_neighbors(neighbors, vars=[]):
    """Convert a string of the form 'X: Y Z; Y: Z' into a dict mapping
    regions to neighbors.  The syntax is a region name followed by a ':'
    followed by zero or more region names, followed by ';', repeated for
    each region name.  If you say 'X: Y' you don't need 'Y: X'.
    >>> parse_neighbors('X: Y Z; Y: Z')
    {'Y': ['X', 'Z'], 'X': ['Y', 'Z'], 'Z': ['X', 'Y']}
    """
    dict = DefaultDict([])
    for var in vars:
        dict[var] = []
    specs = [spec.split(':') for spec in neighbors.split(';')]
    for (A, Aneighbors) in specs:
        A = A.strip()
        dict.setdefault(A, [])
        for B in Aneighbors.split():
            dict[A].append(B)
            dict[B].append(A)
    return dict

australia = MapColoringCSP(list('RGB'),
                           'SA: WA NT Q NSW V; NT: WA Q; NSW: Q V; T: ')

usa = MapColoringCSP(list('RGBY'),
        """WA: OR ID; OR: ID NV CA; CA: NV AZ; NV: ID UT AZ; ID: MT WY UT;
        UT: WY CO AZ; MT: ND SD WY; WY: SD NE CO; CO: NE KA OK NM; NM: OK TX;
        ND: MN SD; SD: MN IA NE; NE: IA MO KA; KA: MO OK; OK: MO AR TX;
        TX: AR LA; MN: WI IA; IA: WI IL MO; MO: IL KY TN AR; AR: MS TN LA;
        LA: MS; WI: MI IL; IL: IN KY; IN: OH KY; MS: TN AL; AL: TN GA FL;
        MI: OH IN; OH: PA WV KY; KY: WV VA TN; TN: VA NC GA; GA: NC SC FL;
        PA: NY NJ DE MD WV; WV: MD VA; VA: MD DC NC; NC: SC; NY: VT MA CT NJ;
        NJ: DE; DE: MD; MD: DC; VT: NH MA; MA: NH RI CT; CT: RI; ME: NH;
        HI: ; AK: """)

france = MapColoringCSP(list('RGBY'),
        """AL: LO FC; AQ: MP LI PC; AU: LI CE BO RA LR MP; BO: CE IF CA FC RA
        AU; BR: NB PL; CA: IF PI LO FC BO; CE: PL NB NH IF BO AU LI PC; FC: BO
        CA LO AL RA; IF: NH PI CA BO CE; LI: PC CE AU MP AQ; LO: CA AL FC; LR:
        MP AU RA PA; MP: AQ LI AU LR; NB: NH CE PL BR; NH: PI IF CE NB; NO:
        PI; PA: LR RA; PC: PL CE LI AQ; PI: NH NO CA IF; PL: BR NB CE PC; RA:
        AU BO FC PA LR""")

#______________________________________________________________________________
# n-Queens Problem

def queen_constraint(A, a, B, b):
    """Constraint is satisfied (true) if A, B are really the same variable,
    or if they are not in the same row, down diagonal, or up diagonal."""
    return A == B or (a != b and A + a != B + b and A - a != B - b)

class NQueensCSP(CSP):
    """Make a CSP for the nQueens problem for search with min_conflicts.
    Suitable for large n, it uses only data structures of size O(n).
    Think of placing queens one per column, from left to right.
    That means position (x, y) represents (var, val) in the CSP.
    The main structures are three arrays to count queens that could conflict:
        rows[i]      Number of queens in the ith row (i.e val == i)
        downs[i]     Number of queens in the \ diagonal
                     such that their (x, y) coordinates sum to i
        ups[i]       Number of queens in the / diagonal
                     such that their (x, y) coordinates have x-y+n-1 = i
    We increment/decrement these counts each time a queen is placed/moved from
    a row/diagonal. So moving is O(1), as is nconflicts.  But choosing
    a variable, and a best value for the variable, are each O(n).
    If you want, you can keep track of conflicted vars, then variable
    selection will also be O(1).
    >>> len(backtracking_search(NQueensCSP(8)))
    8
    """
    def __init__(self, n):
        """Initialize data structures for n Queens."""
        CSP.__init__(self, range(n), UniversalDict(range(n)),
                     UniversalDict(range(n)), queen_constraint)
        update(self, rows=[0]*n, ups=[0]*(2*n - 1), downs=[0]*(2*n - 1))

    def nconflicts(self, var, val, assignment):
        """The number of conflicts, as recorded with each assignment.
        Count conflicts in row and in up, down diagonals. If there
        is a queen there, it can't conflict with itself, so subtract 3."""
        n = len(self.vars)
        c = self.rows[val] + self.downs[var+val] + self.ups[var-val+n-1]
        if assignment.get(var, None) == val:
            c -= 3
        return c

    def assign(self, var, val, assignment):
        "Assign var, and keep track of conflicts."
        oldval = assignment.get(var, None)
        if val != oldval:
            if oldval is not None: # Remove old val if there was one
                self.record_conflict(assignment, var, oldval, -1)
            self.record_conflict(assignment, var, val, +1)
            CSP.assign(self, var, val, assignment)

    def unassign(self, var, assignment):
        "Remove var from assignment (if it is there) and track conflicts."
        if var in assignment:
            self.record_conflict(assignment, var, assignment[var], -1)
        CSP.unassign(self, var, assignment)

    def record_conflict(self, assignment, var, val, delta):
        "Record conflicts caused by addition or deletion of a Queen."
        n = len(self.vars)
        self.rows[val] += delta
        self.downs[var + val] += delta
        self.ups[var - val + n - 1] += delta

    def display(self, assignment):
        "Print the queens and the nconflicts values (for debugging)."
        n = len(self.vars)
        for val in range(n):
            for var in range(n):
                if assignment.get(var,'') == val: ch = 'Q'
                elif (var+val) % 2 == 0: ch = '.'
                else: ch = '-'
                print ch,
            print '    ',
            for var in range(n):
                if assignment.get(var,'') == val: ch = '*'
                else: ch = ' '
                print str(self.nconflicts(var, val, assignment))+ch,
            print

#______________________________________________________________________________
# Sudoku

import itertools, re

lista = [[] for x in xrange(44)]

def subset_sum(k,num,numbers, target, partial=[]):   			#sinartisi p paragei ta domain ton hidden variables
    
    s = sum(partial)

    # check if the partial sum is equals to target
    if s == target: 
        #print len(partial)
        if num==len(partial):
          #print "sum(%s)=%s" % (partial, target)
          #print k
          lista[k].append(partial)
    if s >= target:
        return  # if we reach the number why bother to continue

    for i in range(len(numbers)):
        n = numbers[i]
        remaining = numbers[i+1:]
        subset_sum(k,num,remaining, target, partial + [n]) 



def my_values_constraint(A, a, B, b):      #analoga me to onoma tsekaroume an einai hidden i original variable
    "A constraint saying two neighboring variables must differ in value."
    if A<81 and B<81:
        return a!=b
    elif A>81 and B<81:
        if b in a:
            return 1
        else:
            return 0
    elif A<81 and B>81:
        if a in b:
            return 1
        else:
            return 0    

    return a != b

def domain_routine(a,b):
    """Constraint is satisfied (true) if A, B are really the same variable,
    or if they are not in the same row, down diagonal, or up diagonal."""
    return A == B or (a != b and A + a != B + b and A - a != B - b)

def flatten(seqs): return sum(seqs, [])


sentence= 'AABBBCDEFGGHHCCDEFGGIICJKKFLMMINJKOFLPPQNJOORSPTQNUVVRSTTQWUUXXSYZWWaaXXSYZWbbbcc'
#'AABBBCDEFGGHHCCDEFGGIICJKKFLMMINJKOFLPPQNJOORSPTQNUVVRSTTQWUUXXSYZWWaaXXSYZWbbbcc'
sums=[3,15,22,4,16,15,25,17,9,8,20,6,14,17,17,13,20,12,27,6,20,6,10,14,8,16,15,13,17]
#prepei to sentence na simpiptei me to problem gia paadeigma i thesi 0 t problem exei 2 stoixeia ara theloume dio AA gia BBB ktlp
class Sudoku(CSP):
	
    
    
    R3 = range(3)
    Cell = itertools.count().next
    bgrid = [[[[Cell() for x in R3] for y in R3] for bx in R3] for by in R3]
    boxes = flatten([map(flatten, brow)       for brow in bgrid])
    rows  = flatten([map(flatten, zip(*brow)) for brow in bgrid])
    cols  = zip(*rows)
    problem = [
            [ 3, [0, 1]],
            [15, [2,9,10]],
            [22, [11,13,14,16]],
            [ 4, [18,21]],
            [16, [19,22]],
            [15, [20,23,26,47]],
            [25, [3,4,6,7]],
            [17, [5,12]],
            [ 9, [8,15,36]],
            [ 8, [17,38,41]],
            [20, [24,25,45]],
            [ 6, [27,30]],
            [14, [28,29]],
            [17, [37,40,43]],
            [17, [46,48,49]],            
            [13, [31,32,34]],
            [20, [39,42,63]],
            [12, [50,53]],
            [27, [33,54,57,60]],
            [ 6, [35,55,56]],
            [20, [44,65,72]],
            [ 6, [51,52]],
            [10, [64,66,67,69]],
            [14, [73,74,76,77]],
            [ 8, [58,61]],
            [16, [59,62]],
            [15, [68,75]],
            [13, [70,71,78]],
            [17, [79,80]]]
    
    size=len(sums)+1+80
    numofcages=len(sums)+1
    alfavita=list()
    for i in range(26):
    	alfavita.append(sentence.count(chr(i+65)))       #ftiaxnw mia lista stin opoia metraw apto kathe gramma poso exw
    for i in range(26):
    	alfavita.append(sentence.count(chr(i+97)))
    
    domain_list=list()
    for i in range(len(sums)):
        x=[alfavita[i],sums[i]]    #sto domain list vazoume prwto stoixeio poses fores emfanizete to gramma kai deutero to athroisma
        domain_list.append(x)        

    for i in range(len(domain_list)):
      
      subset_sum(i,domain_list[i][0],[1,2,3,4,5,6,7,8,9],domain_list[i][1])
    
    cage=list()
    x=0
    for i in problem:
    	cage.append(problem[x][1])
        x=x+1
    
    neighbors = dict([(v, set()) for v in range(size)])
    
    for unit in map(set, boxes + rows + cols+cage):
        for v in unit:
            neighbors[v].update(unit - set([v]))
    for i in range(81,size):
          neighbors[i].update(tuple(problem[i-81][1]))
    
    geitones=dict([(v, set()) for v in range(numofcages)])
    
    lista3=[0]*81
    
    for s in range(numofcages-1):
    	for item in problem[s][1]:
        	 lista3[item]=s                 #gia kathe keli vriskw se pia omada anikei   
    
    lista4 = [[] for x in xrange(numofcages-1)]
    
    for s in range(numofcages-1):
        for item in problem[s][1]:
            for koala in neighbors[item]:
                  lista4[s].append(lista3[koala])
   
    for i in range(len(lista4)):
         lista4[i]=list(set(lista4[i]))
    
    for i in range(numofcages-1):
    	geitones[i]=lista4[i]
    
    for i in range(81):
          neighbors[i].add(lista3[i]+81)
    
    count=0  
       
    def __init__(self, grid):
        """Build a Sudoku problem from a string representing the grid:
        the digits 1-9 denote a filled cell, '.' or '0' an empty one;
        other characters are ignored."""
       
        squares = iter(re.findall(r'[a-z]|[A-Z]', grid))
        hidden_squares=iter(re.findall(r'[a-z]|[A-Z]',"ABCDEFGHIJKLMNOPQRSTUVWXYZabc"))
        hidden_domains=dict((var,lista[var-81])
                       for var in range(81,self.size))
        
        domains = dict((var, [1,2,3,4,5,6,7,8,9])
                       for var in  range(81))
       
        
        domains.update(hidden_domains)
             
        
	
        CSP.__init__(self, None, domains, self.neighbors,
                     my_values_constraint)
        
    def display(self, assignment):
        def show_box(box): return [' '.join(map(show_cell, row)) for row in box]
        def show_cell(cell): return str(assignment.get(cell, '.'))
        def abut(lines1, lines2): return map(' | '.join, zip(lines1, lines2))
        print '\n------+-------+------\n'.join(
            '\n'.join(reduce(abut, map(show_box, brow))) for brow in self.bgrid)
     


	
#______________________________________________________________________________
# The Zebra Puzzle

def Zebra():
    "Return an instance of the Zebra Puzzle."
    Colors = 'Red Yellow Blue Green Ivory'.split()
    Pets = 'Dog Fox Snails Horse Zebra'.split()
    Drinks = 'OJ Tea Coffee Milk Water'.split()
    Countries = 'Englishman Spaniard Norwegian Ukranian Japanese'.split()
    Smokes = 'Kools Chesterfields Winston LuckyStrike Parliaments'.split()
    vars = Colors + Pets + Drinks + Countries + Smokes
    domains = {}
    for var in vars:
        domains[var] = range(1, 6)
    domains['Norwegian'] = [1]
    domains['Milk'] = [3]
    neighbors = parse_neighbors("""Englishman: Red;
                Spaniard: Dog; Kools: Yellow; Chesterfields: Fox;
                Norwegian: Blue; Winston: Snails; LuckyStrike: OJ;
                Ukranian: Tea; Japanese: Parliaments; Kools: Horse;
                Coffee: Green; Green: Ivory""", vars)
    for type in [Colors, Pets, Drinks, Countries, Smokes]:
        for A in type:
            for B in type:
                if A != B:
                    if B not in neighbors[A]: neighbors[A].append(B)
                    if A not in neighbors[B]: neighbors[B].append(A)
    def zebra_constraint(A, a, B, b, recurse=0):
        same = (a == b)
        next_to = abs(a - b) == 1
        if A == 'Englishman' and B == 'Red': return same
        if A == 'Spaniard' and B == 'Dog': return same
        if A == 'Chesterfields' and B == 'Fox': return next_to
        if A == 'Norwegian' and B == 'Blue': return next_to
        if A == 'Kools' and B == 'Yellow': return same
        if A == 'Winston' and B == 'Snails': return same
        if A == 'LuckyStrike' and B == 'OJ': return same
        if A == 'Ukranian' and B == 'Tea': return same
        if A == 'Japanese' and B == 'Parliaments': return same
        if A == 'Kools' and B == 'Horse': return next_to
        if A == 'Coffee' and B == 'Green': return same
        if A == 'Green' and B == 'Ivory': return (a - 1) == b
        if recurse == 0: return zebra_constraint(B, b, A, a, 1)
        if ((A in Colors and B in Colors) or
            (A in Pets and B in Pets) or
            (A in Drinks and B in Drinks) or
            (A in Countries and B in Countries) or
            (A in Smokes and B in Smokes)): return not same
        raise 'error'
    return CSP(vars, domains, neighbors, zebra_constraint)

def solve_zebra(algorithm=min_conflicts, **args):
    z = Zebra()
    ans = algorithm(z, **args)
    for h in range(1, 6):
        print 'House', h,
        for (var, val) in ans.items():
            if val == h: print var,
        print
    return ans['Zebra'], ans['Water'], z.nassigns, ans


__doc__ += random_tests("""
>>> min_conflicts(australia)
{'WA': 'B', 'Q': 'B', 'T': 'G', 'V': 'B', 'SA': 'R', 'NT': 'G', 'NSW': 'G'}
>>> min_conflicts(NQueensCSP(8), max_steps=10000)
{0: 5, 1: 0, 2: 4, 3: 1, 4: 7, 5: 2, 6: 6, 7: 3}
""")
