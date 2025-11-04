import MyLean.MyDataStructures.BinTree

open BinTree

#eval Queue.mk (Stack.list_to_stack [1, 3, 5]) (Stack.list_to_stack [5, 2, 2])

def mytree1 := BinTree.node 2 (node 3 empty empty) (node 5 empty empty)
def mytree2 := node 6 (node 8 empty mytree1) (node 7 empty mytree1)

def empty_q := (Queue.empty : Queue (BinTree ℕ))

def myqueue1 := Queue.enqueue mytree1 empty_q
def myqueue2 := Queue.enqueue mytree2 myqueue1

#eval mytree1
#eval mytree2

#eval size mytree1
#eval size mytree2
#eval size' mytree1
#eval size' mytree2

#eval Bi_to_List_df mytree2
#eval Bi_to_List_bf mytree2
