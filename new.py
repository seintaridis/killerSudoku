from test import *
import itertools, re

h = Sudoku(harder1)
None != backtracking_search(h, select_unassigned_variable=mrv, inference=forward_checking)
h.display(h.infer_assignment())
