from csp import *
import itertools, re

print "1.BT"
print "2.BT+MRV"
print "3.FC"
print "4.FC+MRV"""


choice=raw_input("Give choice: ").split() #take choice
choice=int(choice.pop())
print "\n"
h = Sudoku(sentence)
if choice is 1: #call the appropriate function depending of the choice 
    print "BT"
    start = time.clock()
    
    #u = backtracking_search(h,select_unassigned_variable=mrv, inference=forward_checking)
    u = backtracking_search(h)
    elapsed = (time.clock() - start)
elif choice is 2:
	print "BT+MRV"
	start = time.clock()
	u = backtracking_search(h,select_unassigned_variable=mrv)
	elapsed = (time.clock() - start)
elif choice is 3:
	print "FC"
	start = time.clock()
	u = backtracking_search(h,inference=forward_checking)
	elapsed = (time.clock() - start)
elif choice is 4:
	print "FC+MRV"
	start = time.clock()
	u= backtracking_search(h,select_unassigned_variable=mrv, inference=forward_checking)
	elapsed = (time.clock() - start)
#u = backtracking_search(h,select_unassigned_variable=mrv, inference=forward_checking)
#None != backtracking_search(h, select_unassigned_variable=mrv, inference=forward_checking)
h.display(h.infer_assignment())
print "Explored Nodes: ",h.nassigns
print "Arc consistency: ",h.count
print "Elapsed time: ",elapsed," sec"
