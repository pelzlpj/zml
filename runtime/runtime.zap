.NEW 5   ; Specify output format as Z-machine version 5

; Place Z-machine header in first 64 bytes
.INSERT "header.zap"

; Place array of globals in bytes [64, 64 + 240*2 == 544)
.INSERT "globals.zap"

; Last word in the lower 64K is reserved for the 'main' routine (initial
; PC must be represented in two bytes for storage in the header). So, 
; subtracting off the size of the globals and header, 65534-544=64990
; gives us the RAM remaining for heap usage.  Here is the value in words:
HEAP_WORDS=32495

; We set the high bit to indicate a memory block which is a freelist cons cell
FREELIST_BIT=32768
FREELIST_SIZE_MASK=32767

; Zero is a valid freelist location, so we have to choose something different
; for NULL
FREELIST_NULL=65535

WORDREF_HEADER=0     ; Header word for a word-reference cell


; Insert zeros for the empty space until end of dynamic area
__heap_start::
.INSERT "empty_heap.zap"

__begin_static::
__begin_high::

__zml_main::
   call_1n __zml_init_heap
   call_1n __main
   quit


.FUNCT __main, ref1, ref2
   call_2s zml_alloc_wordref 16 -> ref1
   print "Allocated word ref1: "
   print_num ref1
   new_line
   call_2s zml_alloc_wordref 32 -> ref2
   print "Allocated word ref2: "
   print_num ref2
   new_line
   call_2s zml_wordref_get ref1 -> sp
   call_2s zml_wordref_get ref2 -> sp
   add sp sp -> sp
   call_vn zml_wordref_set ref2 sp
   print "Added values: "
   call_2s zml_wordref_get ref2 -> sp
   print_num sp
   new_line
   save -> sp
   rtrue
   

.FUNCT __zml_init_heap
   ; Initialize the heap with zero words allocated.  We end up with
   ; a freelist with one entry representing the entire heap.
   call_vn __zml_freelist_node_cons 0 HEAP_WORDS FREELIST_NULL
   store 'freelist_head 0
   store 'freelist_end  0
   rtrue


.FUNCT zml_alloc_wordref, init_val, ref
   ; Allocate a reference cell which stores a single word.
   ; 
   ; param init_val: the initial value to be stored
   ; local ref: the location of the reference cell
   ;
   ; Returns: word index where reference cell begins (heap-relative)
   call_2s __zml_alloc_block 2 -> ref
   storew __heap_start ref WORDREF_HEADER
   add ref 1 -> sp
   storew __heap_start sp init_val
   ret ref


.FUNCT zml_wordref_get, ref
   ; Retrieve the value stored in a word reference cell.
   ;
   ; param ref: word index where reference cell begins (heap-relative)
   ;
   ; Returns: value
   inc 'ref
   loadw __heap_start ref -> sp
   ret_popped


.FUNCT zml_wordref_set, ref, val
   ; Set the value stored in a word reference cell.
   ;
   ; param ref: word index where reference cell begins (heap-relative)
   ; param  val: new value to place in cell
   inc 'ref
   storew __heap_start ref val
   rtrue


.FUNCT __zml_alloc_block, size_words, curr_node, prev_node, next_node, node_size
   ; Allocate a block of the given size, which shall be an even nonzero value.  If
   ; unsuccessful, the program is aborted with an "out of memory" message.
   ;
   ; param size_words: size of block to be allocated, in words; must be even and >= 2.
   ; local prev_node: pointer to previous freelist node, or FREELIST_INVALID
   ; local curr_node: pointer to current freelist node
   ; local next_node: pointer to next freelist node, or FREELIST_INVALID
   ; local node_size: stores size of a node
   ;
   ; Returns: word index where block begins (heap-relative)
   jeq freelist_head FREELIST_NULL ?end_of_list             ; jump if zero memory available
   store 'prev_node FREELIST_NULL
   load 'freelist_head -> curr_node
   call_2s __zml_freelist_node_next curr_node -> next_node
   
try_alloc_node:
   ; preconditions: prev_node, curr_node, next_node all set
   call_2s __zml_freelist_node_size curr_node -> node_size  ; size of current freelist node
   jl node_size size_words ?move_next_node                  ; jump if not enough space to alloc
   jeq node_size size_words ?alloc_entire_node              ; jump if entire node is consumed

   ; divide curr_node into two pieces: an region to be allocated and a new freelist node
   call_vn __zml_freelist_node_divide curr_node size_words
   call_2s __zml_freelist_node_next curr_node -> next_node  ; update next_node to reflect change

alloc_entire_node:
   call_vn __zml_freelist_node_remove prev_node next_node   ; drop curr_node from freelist
   ret curr_node

move_next_node:
   load 'curr_node -> prev_node
   load 'next_node -> curr_node
   jeq curr_node FREELIST_NULL ?end_of_list                 ; jump if last node
   call_2s __zml_freelist_node_next curr_node -> next_node  ; lookup next-node pointer
   jump try_alloc_node

end_of_list:
   print "Out of memory."
   new_line
   quit


.FUNCT __zml_freelist_node_remove, prev_node, next_node
   ; Remove a node from the freelist.
   ;
   ; param prev_node: pointer to previous node in freelist, or FREELIST_NULL
   ; param next_node: pointer to next node in freelist, or FREELIST_NULL
   jeq prev_node FREELIST_NULL ?remove_freelist_head                 ; jump if this is first node in freelist
   call_vn __zml_freelist_node_set_next prev_node next_node          ; prev_node now linked to next_node
   rtrue

remove_freelist_head:
   store 'freelist_head next_node
   rtrue


.FUNCT __zml_freelist_node_divide, node, size_words, new_node
   ; Divides a freelist node into two pieces.
   ;
   ; param node: pointer to node of size >= size_words + 2
   ; param size_words: desired size of first node
   ; local new_node: location of newly created node
   add node size_words -> new_node                             ; set location of new node
   call_2s __zml_freelist_node_next node -> sp                 ; push location of next node
   call_2s __zml_freelist_node_size node -> sp
   sub sp size_words -> sp                                     ; push size of new node
   call_vn __zml_freelist_node_cons new_node sp sp             ; create new node linked to next_node
   call_vn __zml_freelist_node_cons node size_words new_node   ; link old node to new one
   rtrue


.FUNCT __zml_freelist_node_cons, node, size_words, next
   ; Constructs a new freelist node.
   ;
   ; param node: word pointer to node (even)
   ; param size_words: number of words in node (even)
   ; param next: word pointer to next node (even), or FREELIST_NULL
   or size_words FREELIST_BIT -> sp
   storew __heap_start node sp
   inc 'node
   storew __heap_start node next
   rtrue


.FUNCT __zml_freelist_node_size, node
   ; Returns: size of the given freelist node, in words.
   loadw __heap_start node -> sp          ; sp contains freelist node header
   and sp FREELIST_SIZE_MASK -> sp        ; sp contains size word
   ret_popped


.FUNCT __zml_freelist_node_next, node
   ; Returns: next node in the freelist.  Value 0 means end-of-list.
   inc 'node
   loadw __heap_start node -> node
   ret node


.FUNCT __zml_freelist_node_set_next, node, next
   ; Sets the "next node" pointer in freelist entry <node> to the value <next>.
   inc 'node
   storew __heap_start node next
   rtrue

   
.END
